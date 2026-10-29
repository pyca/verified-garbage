module

public import VerifiedGarbage.Proof.Dsa.X86.RandomScan
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.X86.RandomFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Taint
/-!
# The randomized signer's context (x86)

From the entry state `s₀` (`RandomSignABI`): the 144 bytes of stack below
the return address, from `rLow s₀`, hold the callee's return address and
stack (24 bytes) and the frame (`rBase s₀`, `Random.frameBytes`). The body writes
only that stack, `out`, `scratch` and `used` (`rWrites`), so it reads the
caller's arguments and input bytes as they were on entry (`Ready`).
-/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/RandomSignABI.lean`, which only this module imported.
section

/-!
# The randomized signer's resources, from the shared cdecl contract

Its arguments: `out`, `out_len`, `used`, `key`, `key_len`, `p_len`, `q_len`,
`digest`, `digest_len`, `rand`, `rand_len`, `scratch`, `scratch_len`. The
232 bytes of stack below the return address hold its frame and the call of
the supplied-nonce signer.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

/-- The region of buffer argument `i`, of `n` bytes. -/
abbrev argRegion (s : State) (i n : Nat) : Region := ⟨argumentPointer s i, n⟩

structure RandomSignABI (s : State) : Prop where
  stackLow : 232 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 52 ≤ 2 ^ 32
  rd : s.rd = [argRegion s 3 (arg s 4).toNat, argRegion s 7 (arg s 8).toNat,
    argRegion s 9 (arg s 10).toNat]
  wr : s.wr = [argRegion s 0 (arg s 1).toNat, argRegion s 2 8, argRegion s 11 ((arg s 12).toNat * 8),
    ⟨argAddr s 0, 52⟩]
  outUsed : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 2 8)
  outKey : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 3 (arg s 4).toNat)
  outDigest : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 7 (arg s 8).toNat)
  outRand : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 9 (arg s 10).toNat)
  outScratch : (argRegion s 0 (arg s 1).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  outArgs : (argRegion s 0 (arg s 1).toNat).Disjoint ⟨argAddr s 0, 52⟩
  usedKey : (argRegion s 2 8).Disjoint (argRegion s 3 (arg s 4).toNat)
  usedDigest : (argRegion s 2 8).Disjoint (argRegion s 7 (arg s 8).toNat)
  usedRand : (argRegion s 2 8).Disjoint (argRegion s 9 (arg s 10).toNat)
  usedScratch : (argRegion s 2 8).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  usedArgs : (argRegion s 2 8).Disjoint ⟨argAddr s 0, 52⟩
  keyScratch : (argRegion s 3 (arg s 4).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  keyArgs : (argRegion s 3 (arg s 4).toNat).Disjoint ⟨argAddr s 0, 52⟩
  digestScratch : (argRegion s 7 (arg s 8).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  digestArgs : (argRegion s 7 (arg s 8).toNat).Disjoint ⟨argAddr s 0, 52⟩
  randScratch : (argRegion s 9 (arg s 10).toNat).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  randArgs : (argRegion s 9 (arg s 10).toNat).Disjoint ⟨argAddr s 0, 52⟩
  scratchArgs : (argRegion s 11 ((arg s 12).toNat * 8)).Disjoint ⟨argAddr s 0, 52⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  retUsed : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 2 8)
  retKey : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  retDigest : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat)
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (argRegion s 11 ((arg s 12).toNat * 8))
  stackOutWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat)
  stackUsedWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 2 8)
  stackKeyWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat)
  stackDigestWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat)
  stackRandWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat)
  stackScratchWide : (⟨(s.gpr .esp).setWidth 64 - 232#64, 232⟩ : Region).Disjoint
    (argRegion s 11 ((arg s 12).toNat * 8))
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  usedBound : (arg s 2).toNat + 8 ≤ 2 ^ 32
  keyBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  digestBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  randBound : (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32
  scratchBound : (arg s 11).toNat + (arg s 12).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 5).toNat (arg s 6).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 6).toNat
  keyLength : (arg s 4).toNat = 3 * (arg s 5).toNat + 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (arg s 5).toNat ≤ (arg s 12).toNat

theorem randomSignABI_of {s : State} (h : (Spec.Dsa.randomSignContract abi 232).pre s) :
    RandomSignABI s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem RandomSignABI.stackOut {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 0 (arg s 1).toNat) :=
  A.stackOutWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem RandomSignABI.stackUsed {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 2 8) :=
  A.stackUsedWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem RandomSignABI.stackKey {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 3 (arg s 4).toNat) :=
  A.stackKeyWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem RandomSignABI.stackDigest {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 7 (arg s 8).toNat) :=
  A.stackDigestWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem RandomSignABI.stackRand {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 9 (arg s 10).toNat) :=
  A.stackRandWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

theorem RandomSignABI.stackScratch {s : State} (A : RandomSignABI s) :
    (⟨(s.gpr .esp).setWidth 64 - 144#64, 144⟩ : Region).Disjoint (argRegion s 11 ((arg s 12).toNat * 8)) :=
  A.stackScratchWide.sub_left (fun x hx => Offset.below_mono _ (a := 144) (b := 232) (by decide) (by decide) x hx)

end VG.Proof.Dsa.X86
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-! ## A frame of stack -/

/-- The state after reserving `bytes` bytes of stack. -/
def allocated (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr }

/-- The state after releasing them. -/
def freed (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + BitVec.ofNat 32 bytes) with wr := s.wr.tail }

/-- A frame of `bytes` bytes of stack around a body that never writes `esp`. -/
theorem WP.alloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0) (hsp : bytes ≤ (s.gpr .esp).toNat) (hb : NoSp body)
    (h : WP isa body (allocated bytes s) fun s₂ => Q (freed bytes s₂)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := h
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hb he
  have ha : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
    rfl
  have hf : isa.pop (.free bytes) (allocated bytes s) s₂ = some (freed bytes s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨hn.1, hn.2.1, hn.2.2, hp, hw, ?_⟩
    rfl
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem allocated_esp (n : Nat) (s : State) : (allocated n s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 n :=
  RegUpd.gpr_setReg_self s .esp _
theorem allocated_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (allocated n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne s _ h
theorem allocated_wr (n : Nat) (s : State) :
    (allocated n s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: s.wr := rfl
theorem freed_esp (n : Nat) (s : State) : (freed n s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 n :=
  RegUpd.gpr_setReg_self s .esp _
theorem freed_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (freed n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne s _ h

/-! ## Where things are -/

/-- The lowest byte of the stack the signer uses, 144 bytes below its
return address. -/
def rLow (s₀ : State) : Addr := (s₀.gpr .esp).setWidth 64 - 144#64

/-- The frame's base. -/
def rBase (s₀ : State) : Addr := off (rLow s₀) 24

/-- The lowest byte of the stack the signer's call of `vg_dsa_sign` uses:
the 88 bytes below `rLow` and its 24, for the callee's 108 and the return
address. -/
def rCall (s₀ : State) : Addr := (s₀.gpr .esp).setWidth 64 - 232#64

def rStack (s₀ : State) : Region := ⟨rCall s₀, 232⟩

theorem rLow_eq (s₀ : State) : rLow s₀ = off (rCall s₀) 88 := by
  simp only [rLow, rCall, off]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem rLow_off (s₀ : State) (d : Nat) : off (rLow s₀) d = off (rCall s₀) (88 + d) := by
  rw [rLow_eq, off, off, off, Offset.add_add]
def rOut (s₀ : State) : Region := argRegion s₀ 0 (X86.arg s₀ 1).toNat
def rUsed (s₀ : State) : Region := argRegion s₀ 2 8
def rScratch (s₀ : State) : Region := argRegion s₀ 11 ((X86.arg s₀ 12).toNat * 8)

/-- Where the body may write. -/
def rWrites (s₀ : State) : List Region := [rStack s₀, rOut s₀, rScratch s₀, rUsed s₀]

/-- What the specification reads. -/
def rInput (s₀ : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (X86.arg s₀ 5).toNat
  qLen := (X86.arg s₀ 6).toNat
  key := Spec.Rsa.bytesAt s₀.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat
  digest := Spec.Rsa.bytesAt s₀.mem (argumentPointer s₀ 7) (X86.arg s₀ 8).toNat
  rand := Spec.Rsa.bytesAt s₀.mem (argumentPointer s₀ 9) (X86.arg s₀ 10).toNat

/-- q's bytes, and their address. -/
def rQBytes (s₀ : State) : List Byte := ((rInput s₀).key.drop (rInput s₀).pLen).take (rInput s₀).qLen
def rQ (s₀ : State) : BitVec 32 := X86.arg s₀ 3 + X86.arg s₀ 5

/-- q's significant bytes, and the first of them. -/
abbrev rWidth (s₀ : State) : Nat := (VG.Proof.Dsa.significant (rQBytes s₀)).1
abbrev rLead (s₀ : State) : Byte := (VG.Proof.Dsa.significant (rQBytes s₀)).2

theorem rQ_decode (s₀ : State) :
    Spec.Dsa.decodeBE (rQBytes s₀) =
      (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q := rfl

theorem rBase_off (s₀ : State) (d : Nat) : off (rBase s₀) d = off (rLow s₀) (24 + d) := by
  simp only [rBase, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (A : RandomSignABI s₀)
include A

theorem rLow_toNat : (rLow s₀).toNat = (s₀.gpr .esp).toNat - 144 := by
  have := A.stackLow
  have := (s₀.gpr .esp).isLt
  rw [rLow, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (s₀.gpr .esp).toNat) (by omega)]
  omega

theorem rLow_fit {d : Nat} (hd : d ≤ 200) : (rLow s₀).toNat + d ≤ 2 ^ 32 := by
  have := A.stackBound; rw [rLow_toNat A]; omega

theorem off_rLow_toNat {d : Nat} (hd : d ≤ 200) : (off (rLow s₀) d).toNat = (rLow s₀).toNat + d := by
  have := rLow_fit A hd
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem argAddr_eq {j : Nat} (hj : j < 13) : argAddr s₀ j = off (rLow s₀) (148 + 4 * j) := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackBound
  rw [off_rLow_toNat A (by omega), rLow_toNat A, argAddr, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  have := A.stackLow
  omega

theorem rBase_arg {j : Nat} (hj : j < 13) : off (rBase s₀) (argOff j) = argAddr s₀ j := by
  rw [rBase_off, argAddr_eq A hj, show 24 + argOff j = 148 + 4 * j by unfold argOff Random.frameBytes; omega]

/-- The frame reserved on entry. -/
theorem alloc_base : (s₀.gpr .esp - BitVec.ofNat 32 Random.frameBytes).setWidth 64 = rBase s₀ := by
  have := A.stackLow
  rw [show Random.frameBytes = 120 from rfl, Taint.sub_setWidth (by omega), rBase, rLow, off,
    Offset.sub_ofNat_eq _ (show 120 ≤ 144 by decide)]

theorem alloc_rf : RF (allocated Random.frameBytes s₀) (rBase s₀) := by
  refine ⟨by rw [allocated_esp]; exact alloc_base A, ?_, ?_, ?_⟩
  · rw [allocated_wr, alloc_base A]; exact List.mem_cons_self
  · rw [allocated_wr, rBase_arg A (by decide), A.wr]; simp
  · have := rLow_fit A (d := 200) (by decide)
    rw [rBase, off_rLow_toNat A (by decide)]; unfold argOff Random.frameBytes; omega

/-- The arguments' 52 bytes are apart from where the body writes. -/
theorem args_apart : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨argAddr s₀ 0, 52⟩ r := by
  intro r hr
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [argAddr_eq A (by decide), rLow_off]
    exact Offset.disjoint_base (rCall s₀) (by decide) (by decide)
  · exact A.outArgs.symm
  · exact A.scratchArgs.symm
  · exact A.usedArgs.symm

/-- The return address on entry is apart from the buffers. -/
theorem stack_apart_key : (rStack s₀).Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) := A.stackKeyWide
end

theorem rBytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-! ## The state the body keeps -/

/-- The frame, the permissions of the entry state with the frame, and memory
changed only where the body may write. -/
structure Ready (s₀ t : State) : Prop where
  rf : RF t (rBase s₀)
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, Random.frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

theorem alloc_ready {s₀ : State} (A : RandomSignABI s₀) : Ready s₀ (allocated Random.frameBytes s₀) :=
  ⟨alloc_rf A, rfl, by rw [allocated_wr, alloc_base A], Frame.refl _ _⟩

/-- Registers but `esp` and memory within the stack change. -/
theorem Ready.congr {s₀ t t' : State} {rs : List Reg} (h : Ready s₀ t) (hk : Keeps rs t t')
    (hm : Frame [rStack s₀] t.mem t'.mem) (hsp : .esp ∉ rs := by decide) : Ready s₀ t' :=
  ⟨h.rf.of_keeps hk hsp, hk.2.1.trans h.rd, hk.2.2.trans h.wr,
    h.frame.trans (hm.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])⟩

theorem Ready.upd {s₀ t t' : State} {d : Reg} {v : BitVec 32} (h : Ready s₀ t) (u : Upd t t' d v)
    (hd : d ≠ .esp) : Ready s₀ t' :=
  h.congr (rs := [d]) u.keeps (by rw [u.mem]; exact Frame.refl _ _) (by simpa using hd.symm)

theorem Ready.fupd {s₀ t t' : State} (h : Ready s₀ t) (u : Fupd t t') : Ready s₀ t' :=
  h.congr (rs := []) (u.keeps _) (by rw [u.mem]; exact Frame.refl _ _)

/-- A store to the frame. -/
theorem frame_store (s₀ : State) (m : Mem) {d : Nat} (hd : d + 4 ≤ Random.frameBytes)
    (v : BitVec 32) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off, rLow_off]
  have : Random.frameBytes = 120 := rfl
  exact Offset.contains_base _ (by omega) (by omega)

/-- A byte store to the frame. -/
theorem frame_store8 (s₀ : State) (m : Mem) {d : Nat} (hd : d + 1 ≤ Random.frameBytes)
    (v : BitVec 8) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off, rLow_off]
  have : Random.frameBytes = 120 := rfl
  exact Offset.contains_base _ (by omega) (by omega)

/-- The caller's arguments. -/
theorem Ready.arg {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {j : Nat} (hj : j < 13) :
    t.mem.readW (off (rBase s₀) (argOff j)) 32 = X86.arg s₀ j := by
  rw [rBase_arg A hj, X86.arg]
  refine h.frame.readW (r := ⟨argAddr s₀ j, 4⟩) ?_ (fun r hr => (args_apart A r hr).sub_left ?_) (by decide)
  · exact Offset.contains_base _ (show 0 + 4 ≤ 4 by decide) (by decide) |> fun h => by
      simpa only [BitVec.add_zero] using h
  · rw [argAddr_eq A hj, argAddr_eq A (by decide)]
    exact Offset.sub _ (by omega) (by omega)

theorem Ready.argSrc {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {j : Nat} (hj : j < 13) :
    readSrc t (.mem (Random.arg j)) = some (X86.arg s₀ j) := by
  rw [h.rf.readArgSrc hj, h.arg A hj]

/-- Bytes the body reads, apart from where it writes. -/
theorem Ready.bytes {s₀ t : State} (h : Ready s₀ t) {p : BitVec 32} {n : Nat}
    (hr : (⟨p.setWidth 64, n⟩ : Region) ∈ s₀.rd) (hfit : p.toNat + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨p.setWidth 64, n⟩ r) :
    BytesIn t p (Spec.Rsa.bytesAt s₀.mem (p.setWidth 64) n) := by
  refine ⟨by rw [rBytes_length]; exact hfit, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rBytes_length] at hi
    exact ⟨_, List.mem_append_left _ (h.rd ▸ hr), Offset.contains_base _ (by omega) (by omega)⟩
  · rw [rBytes_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.frame.bytes (R := ⟨p.setWidth 64, n⟩) hd (show n ≤ 2 ^ 64 by omega) hi

theorem Ready.rand {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    BytesIn t (X86.arg s₀ 9) (rInput s₀).rand := by
  refine h.bytes (by rw [A.rd]; simp) A.randBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackRandWide.symm
  · exact A.outRand.symm
  · exact A.randScratch
  · exact A.usedRand.symm

theorem Ready.key {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    BytesIn t (X86.arg s₀ 3) (rInput s₀).key := by
  refine h.bytes (by rw [A.rd]; simp) A.keyBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKeyWide.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

theorem BytesIn.take {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (n : Nat) :
    BytesIn s p (bs.take n) := by
  refine ⟨by rw [List.length_take]; have := h.fit; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_take] at hi; exact h.rd i (by omega)
  · rw [List.length_take] at hi; rw [List.getElem_take]; exact h.val i (by omega)

theorem rQBytes_length {s₀ : State} (A : RandomSignABI s₀) : (rQBytes s₀).length = (X86.arg s₀ 6).toNat := by
  simp only [rQBytes, rInput, List.length_take, List.length_drop, rBytes_length, A.keyLength]
  omega

theorem rQBytes_le {s₀ : State} (A : RandomSignABI s₀) : (rQBytes s₀).length ≤ 32 := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem rQBytes_pos {s₀ : State} (A : RandomSignABI s₀) : 0 < (rQBytes s₀).length := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem Ready.q {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) : BytesIn t (rQ s₀) (rQBytes s₀) := by
  have hk := h.key A
  have hp : (X86.arg s₀ 5).toNat ≤ (rInput s₀).key.length := by
    simp only [rInput, rBytes_length, A.keyLength]; omega
  have := (hk.drop _ hp).take (rInput s₀).qLen
  simpa only [rQ, rQBytes, rInput, BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

end VG.Proof.Dsa.X86
