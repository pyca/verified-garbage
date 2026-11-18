module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! ### `RsaPkcs1Sig.X86_64.VerifyCtx`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the contract on the registers

`verContract` states the shared contract (with the stack the frame and the
call use, `verStack`) on the registers and the stack.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_verify` uses: its
frame, and the return address of its call (whose callee uses none). -/
def verStack : Nat := 2144

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

/-- `vg_rsa_pkcs1_verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx,
hash = r8d, digest = r9, digest_len = [rsp + 8], sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def verContract : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dig : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩
    verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, sig, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      Spec.Rsa.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
      (List.range 5).map (stackArg s₁) = (List.range 5).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `verContract.pre`: a 512-bit modulus, a one-byte `e`, a
one-byte hash value and signature, and the stack arguments at `0x10008`. -/
def verSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10028 then 0x20
    else if a = 0x10008 then 1 else if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x20000, 8448⟩]

theorem leak_eq4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) = (a' ++ b' ++ c' ++ d').map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₂, rfl⟩ := List.append_inj h₁ (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₂ ha
  exact ⟨rfl, rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Sig.X86_64

end

end

/-! ### `RsaPkcs1Sig.X86_64.VerifyFrame`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, the blocks that
store to its slots and read the function's stack arguments, at
`S + frameBytes + 8 + 8 j` (`stackArgAddr`), and the arguments of the call
of `vg_rsa_public_checked` (`pubArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Addresses in the frame -/

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []

/-! ## The precondition, by name -/

/-- `verContract.pre`, by name. -/
structure PreV (s : State) : Prop where
  sp1 : verStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
    ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] s.rd
  hwr : s.wr = [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dds : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dgs : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKg : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wD : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wG : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 1024
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsl : Spec.Rsa.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 verStack

/-- The stack the function uses and the working space: all the function and
its call may write. -/
def stkR (s : State) : Region := ⟨kb s, verStack⟩
def scrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

theorem fb_eq (s : State) : fb s = off (kb s) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : PreV s) : (kb s).toNat + verStack + 48 ≤ 2 ^ 64 ∧
    (kb s).toNat + verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold verStack at *; omega_arith

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]

theorem fb_toNat {s : State} (hp : PreV s) : (fb s).toNat + frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold verStack at *; omega_using [h1])]
  unfold frameBytes verStack at *; omega_using [h1]

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold verStack; omega_using [h])

/-- The return address of a call from the frame. -/
theorem below_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl]
  exact Region.sub_prefix (by decide)

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fb s) 8).Disjoint ⟨off (fb s) d, n⟩ := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_eq, off_off]
  exact Offset.base_disjoint _ (by omega_using []) (by unfold frameBytes at h; omega_using [h])

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega_using [hlt]
  have := frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, scrR s] s.mem t.mem
  sN : word t.mem (fb s) oN = s.gpr .rdi
  sK : word t.mem (fb s) oK = s.gpr .rsi
  sE : word t.mem (fb s) oE = s.gpr .rdx
  sEl : word t.mem (fb s) oEl = s.gpr .rcx
  sH : word t.mem (fb s) oH = s.gpr .r8
  sD : word t.mem (fb s) oD = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreV s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : PreV s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : Env s t) (hp : PreV s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dsa.symm

/-- A word past a store to another word of the frame. -/
theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega_using [hd])).word (by omega_using [h]) (by omega_using [hd'])

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : PreV s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  by
    rw [hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 40⟩, by simp,
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

end VG.Proof.RsaPkcs1Sig.X86_64.Ver

end

end

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the call of `vg_rsa_public_checked`

The arguments kept in the frame's slots and those of the call
(`slotStores_ok`, `callArgs_ok`), what the call writes (`pubWr`), and the
slots it keeps (`slot_keep`, `slot_apart`).

The callee is any code meeting `pubChk`, the contract of
`vg_rsa_public_checked` on the registers: `vg_rsa_public`'s, with BoringSSL's
limits on `e` (`Spec.Rsa.publicOpChecked`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The postcondition of `vg_rsa_public_checked` on the registers. -/
def pubChkPost (s s' : State) : Prop :=
  Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `vg_rsa_public_checked` on the registers: `vg_rsa_public`'s contract,
with BoringSSL's limits on `e`. -/
def pubChk : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post := pubChkPost

/-- An implementation of `vg_rsa_public_checked`, and what its callers need
of it. -/
structure PubImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pubChk.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pubChk.post s s'
  ct : ConstantTime isa pubChk.pre pubChk.pub code
  nosp : NoSp code
  depth : code.depth = 0
  spSafe : code.all (fun i => !isa.writesSp i) = true

end VG.Proof.RsaPkcs1Sig.X86_64

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (sp oN) .rdi, .store (sp oK) .rsi, .store (sp oE) .rdx, .store (sp oEl) .rcx,
    .store (sp oH) .r8, .store (sp oD) .r9]

def callArgs : List Instr :=
  ([.mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rsi, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] : List Instr) ++
  lea .rdi oEM1

theorem pubArgs_eq : pubArgs = slotStores ++ callArgs := rfl

/-- The frame's push and the slots. -/
theorem slotStores_ok {s A : State} (hp : PreV s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block slotStores) A fun t =>
      Keep [.rax] (allocState frameBytes s) t ∧ Outside (fb s) 0 frameBytes s.mem t.mem ∧
      word t.mem (fb s) oN = s.gpr .rdi ∧ word t.mem (fb s) oK = s.gpr .rsi ∧
      word t.mem (fb s) oE = s.gpr .rdx ∧ word t.mem (fb s) oEl = s.gpr .rcx ∧
      word t.mem (fb s) oH = s.gpr .r8 ∧ word t.mem (fb s) oD = s.gpr .r9 := by
  have hF := fb_toNat hp
  have hsp : A.gpr .rsp = fb s := hA.gpr (by decide)
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega_arith)
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → A.gpr r = s.gpr r := fun r h h' => by
    rw [hA.gpr (by simpa using h')]; simp [allocState_gpr, h]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oN) (s.gpr .rdi)).writeW (off (fb s) oK) (s.gpr .rsi)).writeW
        (off (fb s) oE) (s.gpr .rdx)).writeW (off (fb s) oEl) (s.gpr .rcx)).writeW (off (fb s) oH)
        (s.gpr .r8)).writeW (off (fb s) oD) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oN) (by decide), hs.st (d := oK) (by decide),
      hs.st (d := oE) (by decide), hs.st (d := oEl) (by decide), hs.st (d := oH) (by decide),
      hs.st (d := oD) (by decide), hAm, g .rdi (by decide) (by decide), g .rsi (by decide) (by decide),
      g .rdx (by decide) (by decide), g .rcx (by decide) (by decide), g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide)]) rfl) fun t ⟨hm, k⟩ => ⟨(hA.trans k).mono (by simp), ?_, ?_⟩
  · rw [hm]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega_arith
    unfold frameBytes at hx hx'
    simp only [oN, oK, oE, oEl, oH, oD] at *
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
  · rw [hm]
    simp (disch := decide) only [word_wo, word_writeW_self, oN, oK, oE, oEl, oH, oD, and_self]

/-- The arguments of `vg_rsa_public_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreV s) (hk : Keep [.rax] (allocState frameBytes s) t)
    (ho : Outside (fb s) 0 frameBytes s.mem t.mem) :
    WP isa (.block callArgs) t fun t' => Keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] t t' ∧
      t'.mem = (((t.mem.writeW (fb s) (stackArg s 1)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
        (off (fb s) 16) (stackArg s 3)).writeW (off (fb s) 24) (stackArg s 4) ∧
      t'.gpr .rdi = off (fb s) oEM1 ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdi ∧
      t'.gpr .rcx = s.gpr .rsi ∧ t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .r9 = s.gpr .rcx := by
  have hF := fb_toNat hp
  have hsp : t.gpr .rsp = fb s := hk.gpr (by decide)
  have hs : Scr t (fb s) frameBytes :=
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega_arith)
  have hrd : t.rd = s.rd := hk.2.1
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = s.gpr r := fun r h h' => by
    rw [hk.gpr (by simpa using h')]; simp [allocState_gpr, h]
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    have h16 : InRegions t.wr (fb s + 16) 8 := hs.st (d := 16) (by decide)
    have h24 : InRegions t.wr (fb s + 24) 8 := hs.st (d := 24) (by decide)
    xrun [callArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp, h0, h8, h16, h24,
      arg_in hp hrd (show 1 < 5 by decide), arg_in hp hrd (show 3 < 5 by decide),
      arg_in hp hrd (show 4 < 5 by decide), arg_outside hp ho (show 1 < 5 by decide),
      arg_outside hp ho (show 3 < 5 by decide), arg_outside hp ho (show 4 < 5 by decide),
      hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
      sx_ofNat (show oEM1 < 2 ^ 31 by decide),
      g .rsi (by decide) (by decide), g .rdx (by decide) (by decide), g .rcx (by decide) (by decide),
      g .rdi (by decide) (by decide)]) rfl |> fun h => WP.mono h fun t' ⟨q, k⟩ => ⟨k, q⟩

/-! ## The call -/

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega_arith]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq]

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨off (fb s) oEM1, (s.gpr .rsi).toNat⟩

/-- What the call writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [em1R s, scrR s]

/-! ## Memory across the call -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- Memory changed by a call from the frame, within regions in the stack
the function uses or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fb s) d, 8⟩ : Region).Disjoint r) : word m' (fb s) d = word m (fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The slots are apart from `EM₁`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreV s) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ oEM1) :
    ∀ r ∈ pubWr s ++ [below (fb s) 8], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have hk2 := hp.k2
  intro r hr
  simp only [pubWr, em1R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by unfold oEM1 at *; omega_arith) (by unfold oEM1 at *; omega_arith)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold oEM1 frameBytes at *; omega_arith)))
  · exact (ret_disjoint s (by unfold oEM1 frameBytes at *; omega_arith)).symm

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
