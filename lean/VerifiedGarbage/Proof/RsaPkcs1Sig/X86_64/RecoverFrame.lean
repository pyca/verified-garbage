module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyFrame
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Recover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `RsaPkcs1Sig.X86_64.RecoverCtx`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the contract on the registers

`recContract` states the shared contract (with the stack the frame and the
call use, `verStack`, as for `vg_rsa_pkcs1_verify`) on the registers and the
stack.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- `vg_rsa_pkcs1_recover(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def recContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩
    verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, sig, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint sig ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      (∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h ∧
        (s.gpr .rsi).toNat = h.len) ∧
      Spec.Rsa.publicScratchWords (s.gpr .rcx).toNat ≤ (stackArg s 4).toNat
  post s s' := ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) h
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      [stackArg s₁ 1, stackArg s₁ 2, stackArg s₁ 3, stackArg s₁ 4] =
        [stackArg s₂ 1, stackArg s₂ 2, stackArg s₂ 3, stackArg s₂ 4] ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `recContract.pre`: a 512-bit modulus, a one-byte `e`,
MD5 (16-byte values), a one-byte signature, and the stack arguments at
`0x10008`. -/
def recSatState : State where
  gpr r := match r with
    | .rdi => 0x5000 | .rsi => 16 | .rdx => 0x1000 | .rcx => 64 | .r8 => 0x2000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10028 then 0x20
    else if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x5000, 16⟩, ⟨0x20000, 8448⟩]

theorem leak_eq3 {a b c a' b' c' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (h : (a ++ b ++ c).map (·.toNat) = (a' ++ b' ++ c').map (·.toNat)) : a = a' ∧ b = b' ∧ c = c' := by
  have hi : a ++ b ++ c = a' ++ b' ++ c' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₁ ha
  exact ⟨rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Sig.X86_64

end

end


/-!
# `vg_rsa_pkcs1_recover` on x86-64: the frame

`vg_rsa_pkcs1_verify`'s frame (`Ver.fb`, `Ver.stkR`, the working space at the
same stack arguments, `Ver.scrR`), with `out` written too, and other slots.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea)

/-! ## The precondition, by name -/

/-- `recContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  sp1 : verStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] s.rd
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dgs : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKg : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wG : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h ∧ (s.gpr .rsi).toNat = h.len
  hsl : Spec.Rsa.publicScratchWords (s.gpr .rcx).toNat ≤ (stackArg s 4).toNat

/-- `out_len` is the length of the hash function's values: from 16 to 64. -/
theorem PreR.ol {s : State} (hp : PreR s) : 16 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64 := by
  obtain ⟨h, -, hl⟩ := hp.hash
  rw [hl]; cases h <;> decide

/-! ## The frame -/

def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩

theorem kb_toNat {s : State} (hp : PreR s) : (kb s).toNat + verStack + 48 ≤ 2 ^ 64 ∧
    (kb s).toNat + verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold verStack at *; omega_arith

theorem fb_toNat {s : State} (hp : PreR s) : (fb s).toNat + frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold verStack at *; omega_using [h1])]
  unfold frameBytes verStack at *; omega_using [h1]

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sOl : word t.mem (fb s) oOl = s.gpr .rsi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreR s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : PreR s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : Env s t) (hp : PreR s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : PreR s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  by
    rw [hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 40⟩, by simp,
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
