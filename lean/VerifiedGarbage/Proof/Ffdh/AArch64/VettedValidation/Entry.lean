module

public import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Save the public input arguments and initialize an unmatched recognition sentinel. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem execAdr (s : State) (r : Reg) (sym : String) :
  exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) := rfl

def entryMemory (m : Mem) (B dom dl k words : Addr) : Mem :=
  ((((m.writeW (off B (8*sDom)) dom).writeW (off B (8*sDL)) dl).writeW
    (off B (8*sLen)) k).writeW (off B (8*sCtx)) words).writeW (off B (8*sBits)) (4095#64)

theorem entry_ok {s : State} {B : Addr} {Z : Nat}
    (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x3=B) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.entry) s fun t =>
    (t.gpr .x0=B ∧ t.gpr .x4=s.syms Policy.tableSym ∧ t.gpr .x7=10#64 ∧
      t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4)) ∧
    Keep [.x0,.x4,.x7,.x10] s t := by
  refine WP.keep [.x0,.x4,.x7,.x10] ?_ rfl rfl rfl
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.entry entryMemory
  brun [base,st,execAdr,hdr_enc (show sBits<32 by decide),
    scratch.st (d:=8*sDom) (by unfold sDom;omega),
    scratch.st (d:=8*sDL) (by unfold sDL;omega),
    scratch.st (d:=8*sLen) (by unfold sLen;omega),
    scratch.st (d:=8*sCtx) (by unfold sCtx;omega),
    scratch.st (d:=8*sBits) (by unfold sBits;omega)]
  exact ⟨rfl,rfl⟩

theorem entryMemory_header (m : Mem) (B dom dl k words : Addr) :
    word (entryMemory m B dom dl k words) B (8*sDom)=dom ∧
    word (entryMemory m B dom dl k words) B (8*sDL)=dl ∧
    word (entryMemory m B dom dl k words) B (8*sLen)=k ∧
    word (entryMemory m B dom dl k words) B (8*sCtx)=words ∧
    word (entryMemory m B dom dl k words) B (8*sBits)=4095#64 := by
  have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
      word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
    Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)
  unfold entryMemory
  rw [separate _ sBits sDom (by decide) (by decide) (by decide),separate _ sCtx sDom (by decide) (by decide) (by decide),
    separate _ sLen sDom (by decide) (by decide) (by decide),separate _ sDL sDom (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sDL (by decide) (by decide) (by decide),separate _ sCtx sDL (by decide) (by decide) (by decide),
    separate _ sLen sDL (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sLen (by decide) (by decide) (by decide),separate _ sCtx sLen (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sCtx (by decide) (by decide) (by decide),word_writeW_self,word_writeW_self]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem entryMemory_range (m : Mem) (B dom dl k words : Addr) :
    Outside B 128 40 m (entryMemory m B dom dl k words) := by
  intro x hx
  have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<21) (v : Addr) :
      (m.writeW (off B (8*i)) v) x=m x :=
    writeW_outside m B v (by omega) x (by omega)
  unfold entryMemory
  rw [store _ sBits (by decide) (by decide),store _ sCtx (by decide) (by decide),
    store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
    store _ sDom (by decide) (by decide)]

end VG.Proof.Ffdh.AArch64.VettedValidation
