// Copyright (c) 2023- PPSSPP Project.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 2.0 or later versions.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License 2.0 for more details.

// A copy of the GPL 2.0 should have been included with the program.
// If not, see http://www.gnu.org/licenses/

// Official git repository and contact information can be found at
// https://github.com/hrydgard/ppsspp and http://www.ppsspp.org/.

#include "ppsspp_config.h"
// In other words, PPSSPP_ARCH(ARM64) || DISASM_ALL.
#if PPSSPP_ARCH(ARM64) || (PPSSPP_PLATFORM(WINDOWS) && !defined(__LIBRETRO__))

#include <cstddef>
#include <map>
#include "Common/Log.h"
#include "Core/MemMap.h"
#include "Core/MIPS/MIPSTables.h"
#include "Core/MIPS/ARM64/Arm64IRJit.h"
#include "Core/MIPS/ARM64/Arm64IRRegCache.h"

#include <algorithm>
// for std::min

namespace MIPSComp {

using namespace Arm64Gen;
using namespace Arm64IRJitConstants;

// Invalidations just need at most two MOVs and B.
static constexpr int MIN_BLOCK_NORMAL_LEN = 12;
// As long as we can fit a B, we should be fine.
static constexpr int MIN_BLOCK_EXIT_LEN = 4;

Arm64JitBackend::Arm64JitBackend(JitOptions &jitopt)
	: jo(jitopt), regs_(&jo), fp_(this) {
	// Automatically disable incompatible options. Pointerify also depends on the CPU's memory base,
	// checked in GenerateFixedCode().
	jo.optimizeForInterpreter = false;
#ifdef MASKED_PSP_MEMORY
	jo.enablePointerify = false;
#endif

	// Since we store the offset, this is as big as it can be.
	AllocCodeSpace(NATIVE_CODE_SPACE_SIZE);

	regs_.Init(this, &fp_);
}

Arm64JitBackend::~Arm64JitBackend() {}

void Arm64JitBackend::UpdateFCR31(MIPSState *mipsState) {
	currentRoundingFunc_ = convertS0ToSCRATCH1_[mipsState->fcr31 & 3];
}

// Temporary iOS-only instruction-by-instruction trace for Cube Sample's startup.
// Captures the guest state before every emitted IR instruction in the selected blocks.
// This intentionally flushes register caches, so it may affect a register-allocation bug.
#if PPSSPP_PLATFORM(IOS)
static u32 g_cubeTraceStep = 0;
static constexpr u32 CUBE_TRACE_MAX_STEPS = 8192;

static void TraceCubeIRStep(MIPSState *mips, u32 blockPC, u32 irIndex, u64 encodedIR) {
	if (!mips || g_cubeTraceStep >= CUBE_TRACE_MAX_STEPS)
		return;
	const u32 seq = ++g_cubeTraceStep;
	const IROp op = (IROp)(encodedIR & 0xff);
	const IRMeta *meta = GetIRMeta(op);
	const u32 dest = (u32)((encodedIR >> 8) & 0xff);
	const u32 src1 = (u32)((encodedIR >> 16) & 0xff);
	const u32 src2 = (u32)((encodedIR >> 24) & 0xff);
	const u32 constant = (u32)(encodedIR >> 32);
	const u32 sp = mips->r[MIPS_REG_SP];
	const auto stackWord = [sp](u32 offset) -> u32 {
		const u32 address = sp + offset;
		return Memory::IsValid4AlignedAddress(address) ? Memory::ReadUnchecked_U32(address) : 0;
	};
	ERROR_LOG(Log::MemMap,
		"[CUBE-STEP] #%05u block=%08x ir=%03u op=%s d=%u s1=%u s2=%u imm=%08x "
		"pc=%08x sp=%08x ra=%08x v0=%08x a0=%08x a1=%08x",
		seq, blockPC, irIndex, meta ? meta->name : "?", dest, src1, src2, constant,
		mips->pc, sp, mips->r[MIPS_REG_RA], mips->r[MIPS_REG_V0],
		mips->r[MIPS_REG_A0], mips->r[MIPS_REG_A1]);
	ERROR_LOG(Log::MemMap,
		"[CUBE-GPR] #%05u r00-31="
		"%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,"
		"%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,"
		"%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,"
		"%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x",
		seq,
		mips->r[0], mips->r[1], mips->r[2], mips->r[3],
		mips->r[4], mips->r[5], mips->r[6], mips->r[7],
		mips->r[8], mips->r[9], mips->r[10], mips->r[11],
		mips->r[12], mips->r[13], mips->r[14], mips->r[15],
		mips->r[16], mips->r[17], mips->r[18], mips->r[19],
		mips->r[20], mips->r[21], mips->r[22], mips->r[23],
		mips->r[24], mips->r[25], mips->r[26], mips->r[27],
		mips->r[28], mips->r[29], mips->r[30], mips->r[31]);
	ERROR_LOG(Log::MemMap,
		"[CUBE-STACK] #%05u sp=%08x words[+00..+2c]="
		"%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x",
		seq, sp, stackWord(0), stackWord(4), stackWord(8), stackWord(12),
		stackWord(16), stackWord(20), stackWord(24), stackWord(28),
		stackWord(32), stackWord(36), stackWord(40), stackWord(44));
	if (seq == CUBE_TRACE_MAX_STEPS) {
		ERROR_LOG(Log::MemMap, "[CUBE-STEP-LIMIT] Stopped after %u steps; restart PPSSPP for a new trace.", seq);
	}
}
#endif

static void NoBlockExits() {
	_assert_msg_(false, "Never exited block, invalid IR?");
}

// TODO: Much of this function should be merged with the same function for the other backends.
bool Arm64JitBackend::CompileBlock(int block_num, u32 startPC, const IRInst *instructions, int count) {
	if (GetSpaceLeft() < 0x800)
		return false;

	// An accurate dot product can flush several registers around its call.
	size_t sizeEstimate = 0;
	for (int i = 0; i < count; ++i) {
		switch (instructions[i].op) {
		case IROp::Vec4VfpuDot:
		case IROp::Vec4VfpuMultiDot:
		// The jump to a register looks up the block itself.
		case IROp::ExitToReg:
			sizeEstimate += 96;
			break;
		// The range check and the call-out for hardware registers.
		case IROp::LoadKernel8:
		case IROp::LoadKernel8Ext:
		case IROp::LoadKernel16:
		case IROp::LoadKernel16Ext:
		case IROp::LoadKernel32:
		case IROp::StoreKernel8:
		case IROp::StoreKernel16:
		case IROp::StoreKernel32:
			sizeEstimate += 64;
			break;
		default:
			sizeEstimate += 32;
			break;
		}
	}
#if PPSSPP_PLATFORM(IOS)
	const bool traceCubeBlock = startPC >= 0x08900000 && startPC < 0x08910000;
	// Room for explicit register flush, static-register save, and the trace callback.
	if (traceCubeBlock)
		sizeEstimate += (size_t)count * 256;
#endif
	BeginWrite(std::min(GetSpaceLeft(), sizeEstimate));

	bool wroteCheckedOffset = false;
	if (jo.enableBlocklink && !jo.useBackJump) {
		SetBlockCheckedOffset(block_num, (int)GetOffset(GetCodePointer()));
		wroteCheckedOffset = true;

		WriteDebugPC(startPC);

		// Check the sign bit to check if negative.
		FixupBranch normalEntry = TBZ(DOWNCOUNTREG, 31);
		MOVI2R(SCRATCH1, startPC);
		B(outerLoopPCInSCRATCH1_);
		SetJumpTarget(normalEntry);
	}

	// Don't worry, the codespace isn't large enough to overflow offsets.
	const u8 *blockStart = GetCodePointer();
	SetBlockEntry(block_num, startPC, (int)GetOffset(blockStart));
	compilingBlockNum_ = block_num;
	lastConstPC_ = 0;

	regs_.Start(startPC, instructions, count);

	std::vector<const u8 *> &addresses = irAddresses_;
	addresses.clear();
	addresses.reserve(count);
	compilingInsts_ = instructions;
	compilingCount_ = count;
	for (int i = 0; i < count; ++i) {
		const IRInst &inst = instructions[i];
		regs_.SetIRIndex(i);
		compilingIndex_ = i;
		addresses.push_back(GetCodePtr());

#if PPSSPP_PLATFORM(IOS)
		if (traceCubeBlock) {
			// Capture a consistent guest state before each IR operation.
			// The next snapshot represents the state after the preceding operation.
			FlushAll();
			SaveStaticRegisters();
			const u64 encodedIR = (u64)(u8)inst.op | ((u64)inst.dest << 8) |
				((u64)inst.src1 << 16) | ((u64)inst.src2 << 24) | ((u64)inst.constant << 32);
			MOVP2R(X0, mips_);
			MOVI2R(W1, startPC);
			MOVI2R(W2, (u32)i);
			MOVI2R(X3, encodedIR);
			QuickCallFunction(SCRATCH2_64, &TraceCubeIRStep);
			LoadStaticRegisters();
		}
#endif
		CompileIRInst(inst);
		if (skipNextInst_) {
			// It was compiled together with this one.
			skipNextInst_ = false;
			addresses.push_back(GetCodePtr());
			i++;
		}

		if (jo.Disabled(JitDisable::REGALLOC_GPR) || jo.Disabled(JitDisable::REGALLOC_FPR))
			regs_.FlushAll(jo.Disabled(JitDisable::REGALLOC_GPR), jo.Disabled(JitDisable::REGALLOC_FPR));

		// Safety check, in case we get a bunch of really large jit ops without a lot of branching.
		if (GetSpaceLeft() < 0x800) {
			compilingBlockNum_ = -1;
			return false;
		}
	}

	// We should've written an exit above.  If we didn't, bad things will happen.
	// Only check if debug stats are enabled - needlessly wastes jit space.
	if (DebugStatsEnabled()) {
		QuickCallFunction(SCRATCH2_64, &NoBlockExits);
		B(hooks_.crashHandler);
	}

	int len = (int)GetOffset(GetCodePointer()) - GetBlockEntry(block_num);
	if (len < MIN_BLOCK_NORMAL_LEN) {
		// We need at least 10 bytes to invalidate blocks with.
		ReserveCodeSpace(MIN_BLOCK_NORMAL_LEN - len);
	}

	if (!wroteCheckedOffset) {
		// Always record this, even if block link disabled - it's used for size calc.
		SetBlockCheckedOffset(block_num, (int)GetOffset(GetCodePointer()));
	}

	if (jo.enableBlocklink && jo.useBackJump) {
		WriteDebugPC(startPC);

		// Small blocks are common, check if it's < 32KB long.
		ptrdiff_t distance = blockStart - GetCodePointer();
		if (distance >= -0x8000 && distance < 0x8000) {
			TBZ(DOWNCOUNTREG, 31, blockStart);
		} else {
			FixupBranch toDispatch = TBNZ(DOWNCOUNTREG, 31);
			B(blockStart);
			SetJumpTarget(toDispatch);
		}

		MOVI2R(SCRATCH1, startPC);
		B(outerLoopPCInSCRATCH1_);
	}

	RecordIRAddresses(block_num, addresses);

	if (logBlocks_ > 0) {
		--logBlocks_;

		std::map<const u8 *, int> addressesLookup;
		for (int i = 0; i < (int)addresses.size(); ++i)
			addressesLookup[addresses[i]] = i;

		INFO_LOG(Log::JIT, "=============== ARM64 (%08x, %d bytes) ===============", startPC, len);
		for (const u8 *p = blockStart; p < GetCodePointer(); ) {
			auto it = addressesLookup.find(p);
			if (it != addressesLookup.end()) {
				const IRInst &inst = instructions[it->second];

				char temp[512];
				DisassembleIR(temp, sizeof(temp), inst);
				INFO_LOG(Log::JIT, "IR: #%d %s", it->second, temp);
			}

			auto next = std::next(it);
			const u8 *nextp = next == addressesLookup.end() ? GetCodePointer() : next->first;

			auto lines = DisassembleArm64(p, (int)(nextp - p));
			for (const auto &line : lines)
				INFO_LOG(Log::JIT, " A: %s", line.c_str());
			p = nextp;
		}
	}

	EndWrite();
	// Flushed with the links, after FinalizeBlock.
	const u8 *flushStart, *flushEnd;
	TakeIcacheFlushRange(&flushStart, &flushEnd);
	AddPendingIcacheFlush(flushStart, flushEnd);
	compilingBlockNum_ = -1;

	return true;
}

void Arm64JitBackend::AddPendingIcacheFlush(const u8 *start, const u8 *end) {
	if (numPendingFlushes_ == MAX_PENDING_ICACHE_FLUSHES)
		FlushPendingIcache();
	pendingFlushStarts_[numPendingFlushes_] = start;
	pendingFlushEnds_[numPendingFlushes_] = end;
	numPendingFlushes_++;
}

void Arm64JitBackend::FlushPendingIcache() {
	if (numPendingFlushes_ == 0)
		return;
	FlushIcacheSections(pendingFlushStarts_, pendingFlushEnds_, numPendingFlushes_);
	numPendingFlushes_ = 0;
}

void Arm64JitBackend::WriteConstExit(uint32_t pc) {
	int block_num = FindBlockByStart(pc);
	const IRNativeBlock *nativeBlock = GetNativeBlock(block_num);

	int exitStart = (int)GetOffset(GetCodePointer());
	if (block_num >= 0 && jo.enableBlocklink && nativeBlock && nativeBlock->checkedOffset != 0) {
		B(GetBasePtr() + nativeBlock->checkedOffset);
	} else {
		MOVI2R(SCRATCH1, pc);
		B(dispatcherPCInSCRATCH1_);
	}

	if (jo.enableBlocklink) {
		// In case of compression or early link, make sure it's large enough.
		int len = (int)GetOffset(GetCodePointer()) - exitStart;
		if (len < MIN_BLOCK_EXIT_LEN) {
			ReserveCodeSpace(MIN_BLOCK_EXIT_LEN - len);
			len = MIN_BLOCK_EXIT_LEN;
		}

		AddLinkableExit(compilingBlockNum_, pc, exitStart, len);
	}
}

void Arm64JitBackend::OverwriteExit(int srcOffset, int len, int block_num) {
	_dbg_assert_(len >= MIN_BLOCK_EXIT_LEN);

	const IRNativeBlock *nativeBlock = GetNativeBlock(block_num);
	if (nativeBlock) {
		u8 *writable = GetWritablePtrFromCodePtr(GetBasePtr()) + srcOffset;
		if (PlatformIsWXExclusive()) {
			ProtectMemoryPages(writable, len, MEM_PROT_READ | MEM_PROT_WRITE);
		}

		ARM64XEmitter emitter(GetBasePtr() + srcOffset, writable);
		emitter.B(GetBasePtr() + nativeBlock->checkedOffset);
		int bytesWritten = (int)(emitter.GetWritableCodePtr() - writable);
		_dbg_assert_(bytesWritten <= MIN_BLOCK_EXIT_LEN);
		if (bytesWritten < len)
			emitter.ReserveCodeSpace(len - bytesWritten);
		// Only called from FinalizeBlock, which flushes.
		AddPendingIcacheFlush(GetBasePtr() + srcOffset, GetBasePtr() + srcOffset + len);

		if (PlatformIsWXExclusive()) {
			ProtectMemoryPages(writable, 16, MEM_PROT_READ | MEM_PROT_EXEC);
		}
	}
}

void Arm64JitBackend::CompIR_Generic(IRInst inst) {
	// If we got here, we're going the slow way.
	uint64_t value;
	memcpy(&value, &inst, sizeof(inst));

	FlushAll();
	SaveStaticRegisters();
	WriteDebugProfilerStatus(IRProfilerStatus::IR_INTERPRET);
	MOVI2R(X0, value);
	MOVP2R(X1, mips_);
	QuickCallFunction(SCRATCH2_64, &DoIRInst);
	WriteDebugProfilerStatus(IRProfilerStatus::IN_JIT);
	LoadStaticRegisters();

	// We only need to check the return value if it's a potential exit.
	if ((GetIRMeta(inst.op)->flags & IRFLAG_EXIT) != 0) {
		MOV(SCRATCH1, X0);

		ptrdiff_t distance = dispatcherPCInSCRATCH1_ - GetCodePointer();
		if (distance >= -0x100000 && distance < 0x100000) {
			// Convenient, we can do a simple branch if within 1MB.
			CBNZ(W0, dispatcherPCInSCRATCH1_);
		} else {
			// That's a shame, we need a long branch.
			FixupBranch keepOnKeepingOn = CBZ(W0);
			B(dispatcherPCInSCRATCH1_);
			SetJumpTarget(keepOnKeepingOn);
		}
	}
}

void Arm64JitBackend::CompIR_Interpret(IRInst inst) {
	MIPSOpcode op(inst.constant);

	// IR protects us against this being a branching instruction (well, hopefully.)
	FlushAll();
	SaveStaticRegisters();
	WriteDebugProfilerStatus(IRProfilerStatus::INTERPRET);
	if (DebugStatsEnabled()) {
		MOVP2R(X0, MIPSGetName(op));
		QuickCallFunction(SCRATCH2_64, &NotifyMIPSInterpret);
	}
	MOVI2R(W0, inst.constant);
	MOVP2R(X1, mips_);
	QuickCallFunction(SCRATCH2_64, &MIPSInterpretTrampoline);
	WriteDebugProfilerStatus(IRProfilerStatus::IN_JIT);
	LoadStaticRegisters();
}

void Arm64JitBackend::FlushAll() {
	regs_.FlushAll();
}

bool Arm64JitBackend::DescribeCodePtr(const u8 *ptr, std::string &name) const {
	// Used in disassembly viewer and profiling tools.
	// Don't use spaces; profilers get confused or truncate them.
	if (ptr == dispatcherPCInSCRATCH1_) {
		name = "dispatcherPCInSCRATCH1";
	} else if (ptr == outerLoopPCInSCRATCH1_) {
		name = "outerLoopPCInSCRATCH1";
	} else if (ptr == dispatcherNoCheck_) {
		name = "dispatcherNoCheck";
	} else if (ptr == saveStaticRegisters_) {
		name = "saveStaticRegisters";
	} else if (ptr == loadStaticRegisters_) {
		name = "loadStaticRegisters";
	} else if (ptr == restoreRoundingMode_) {
		name = "restoreRoundingMode";
	} else if (ptr == applyRoundingMode_) {
		name = "applyRoundingMode";
	} else if (ptr == updateRoundingMode_) {
		name = "updateRoundingMode";
	} else if (ptr == currentRoundingFunc_) {
		name = "currentRoundingFunc";
	} else if (ptr >= convertS0ToSCRATCH1_[0] && ptr <= convertS0ToSCRATCH1_[7]) {
		name = "convertS0ToSCRATCH1";
	} else if (ptr >= GetBasePtr() && ptr < GetBasePtr() + jitStartOffset_) {
		name = DescribeFixedCode(ptr);
	} else {
		return IRNativeBackend::DescribeCodePtr(ptr, name);
	}
	return true;
}

void Arm64JitBackend::ClearAllBlocks() {
	ClearCodeSpace(jitStartOffset_);
	// Whatever was pending is in there.
	numPendingFlushes_ = 0;
	FlushIcacheSection(region + jitStartOffset_, region + region_size - jitStartOffset_);
	EraseAllLinks(-1);
}

void Arm64JitBackend::InvalidateBlock(int block_num) {
	const IRNativeBlock *nativeBlock = GetNativeBlock(block_num);
	int offset = nativeBlock->entryOffset;
	u8 *writable = GetWritablePtrFromCodePtr(GetBasePtr()) + offset;

	// Overwrite the block with a jump to compile it again.
	u32 pc = nativeBlock->startPC;
	if (pc != 0) {
		// Hopefully we always have at least 16 bytes, which should be all we need.
		if (PlatformIsWXExclusive()) {
			ProtectMemoryPages(writable, MIN_BLOCK_NORMAL_LEN, MEM_PROT_READ | MEM_PROT_WRITE);
		}

		ARM64XEmitter emitter(GetBasePtr() + offset, writable);
		emitter.MOVI2R(SCRATCH1, pc);
		emitter.B(dispatcherPCInSCRATCH1_);
		int bytesWritten = (int)(emitter.GetWritableCodePtr() - writable);
		if (bytesWritten < MIN_BLOCK_NORMAL_LEN)
			emitter.ReserveCodeSpace(MIN_BLOCK_NORMAL_LEN - bytesWritten);
		emitter.FlushIcache();

		if (PlatformIsWXExclusive()) {
			ProtectMemoryPages(writable, MIN_BLOCK_NORMAL_LEN, MEM_PROT_READ | MEM_PROT_EXEC);
		}
	}

	EraseAllLinks(block_num);
}

void Arm64JitBackend::RestoreRoundingMode(bool force) {
	QuickCallFunction(SCRATCH2_64, restoreRoundingMode_);
}

void Arm64JitBackend::ApplyRoundingMode(bool force) {
	QuickCallFunction(SCRATCH2_64, applyRoundingMode_);
}

void Arm64JitBackend::UpdateRoundingMode(bool force) {
	QuickCallFunction(SCRATCH2_64, updateRoundingMode_);
}

void Arm64JitBackend::MovFromPC(ARM64Reg r) {
	LDR(INDEX_UNSIGNED, r, CTXREG, offsetof(MIPSState, pc));
}

void Arm64JitBackend::MovToPC(ARM64Reg r) {
	STR(INDEX_UNSIGNED, r, CTXREG, offsetof(MIPSState, pc));
}

void Arm64JitBackend::WriteDebugPC(uint32_t pc) {
	if (hooks_.profilerPC) {
		int offset = (int)((const u8 *)hooks_.profilerPC - GetBasePtr());
		MOVI2R(SCRATCH2, offset);
		MOVI2R(SCRATCH1, pc);
		STR(SCRATCH1, JITBASEREG, SCRATCH2);
	}
}

void Arm64JitBackend::WriteDebugPC(ARM64Reg r) {
	if (hooks_.profilerPC) {
		int offset = (int)((const u8 *)hooks_.profilerPC - GetBasePtr());
		MOVI2R(SCRATCH2, offset);
		STR(r, JITBASEREG, SCRATCH2);
	}
}

void Arm64JitBackend::WriteDebugProfilerStatus(IRProfilerStatus status) {
	if (hooks_.profilerPC) {
		int offset = (int)((const u8 *)hooks_.profilerStatus - GetBasePtr());
		MOVI2R(SCRATCH2, offset);
		MOVI2R(SCRATCH1, (int)status);
		STR(SCRATCH1, JITBASEREG, SCRATCH2);
	}
}

void Arm64JitBackend::SaveStaticRegisters() {
	if (jo.useStaticAlloc) {
		QuickCallFunction(SCRATCH2_64, saveStaticRegisters_);
	} else {
		// Inline the single operation
		STR(INDEX_UNSIGNED, DOWNCOUNTREG, CTXREG, offsetof(MIPSState, downcount));
	}
}

void Arm64JitBackend::LoadStaticRegisters() {
	if (jo.useStaticAlloc) {
		QuickCallFunction(SCRATCH2_64, loadStaticRegisters_);
	} else {
		LDR(INDEX_UNSIGNED, DOWNCOUNTREG, CTXREG, offsetof(MIPSState, downcount));
	}
}

} // namespace MIPSComp

#endif
