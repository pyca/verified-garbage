module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Batteries.Logic

/-!
# RSASSA-PSS signing on x86-64: correctness

`sign_body`: from the entry state, the body of the frame leaves `out` and
`rax` as `RsaPss.sign` says, with the callee-saved registers restored.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)

variable {G : Spec.Mgf1.Hash}

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

/-- `Rep` across a change that keeps the frame and our working space. -/
theorem Rep.of_keep {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (G' : Geo F S) (hk : ∀ x, ((⟨F, frameBytes⟩ : Region).Contains x 1 ∨ (⟨S, oRsa⟩ : Region).Contains x 1) →
      m' x = m x) : Rep m' F S V W where
  scr o ho := by rw [hk _ (.inr (Offset.contains_base _ (by omega_arith) (by unfold oRsa at *; omega_arith))), R.scr o ho]
  fr k hk' := by
    rw [← R.fr k hk']
    refine Mem.readW_congr fun i hi => hk _ (.inl ?_)
    have := G'.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega_arith) (by unfold nW frameBytes at *; omega_arith)

/-- Memory changed only in the frame. -/
theorem frame_wrR {s : State} {m : Mem} (h : Frame [frR s] s.mem m) : Frame (wrR s) s.mem m :=
  h.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩

/-- Memory changed only in the writable regions and below the frame. -/
theorem frame_keep {s u v : State} (hp : SPre G s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 → v.mem a = u.mem a) :
    Frame (wrR s) s.mem v.mem := by
  intro x hx
  refine (hk x (fun r hr hc => ?_) (fun hc => ?_)).trans (hM x hx)
  · rw [hw, hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hx _ (List.mem_cons_self ..) (frame_sub s x hc)
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hc
    · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) hc
  · rw [hsp] at hc; exact hx _ (List.mem_cons_self ..) (ret_sub s x hc)

variable (G) in
/-- The outcome `signK.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)

variable (G) in
/-- Before the epilogue: the outcome written, the saved registers in their
slots. -/
structure SDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 13)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (signOut G s)
  /-- MXCSR's control bits. -/
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem fail_done {s t : State} (hp : SPre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 13)) (R : Rep t.mem (fb s) (stackArg s 13) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12) (hinv : signOut G s = .invalid) (hmx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    WP isa signFail t (SDone G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [hw, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  refine WP.mono_mx (by decide) (signFail_ok L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) h16
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2 hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun t' ⟨L', k', R', hax, hz, _⟩ hm => ?_
  refine ⟨L', k'.2.2.trans hw, fun r hr => (k'.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans
    (hcs r hr), ?_, ?_, ?_, ?_, by rw [hm]; exact hmx⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · rw [hinv]; exact ⟨by rw [hax]; rfl, hz⟩

/-- Stack arguments, kept where the function does not write. -/
theorem argsKept_of {s : State} (hp : SPre G s) {m : Mem} (hM : Frame (wrR s) s.mem m) : ArgsKept s m := by
  intro j hj
  refine hM.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (in_apart hp.dKa hp.dOa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith]
  have := hp.sp2
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- An input's bytes, unchanged. -/
theorem bytesF_eq {s : State} {m : Mem} (hM : Frame (wrR s) s.mem m) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrR s, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    (List.range n).map (bytesF m p) = Spec.Rsa.bytesAt s.mem p n :=
  bytesAt_frame hM hd hn

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

/-- The state after the frame's pop. -/
def freedF (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 frameBytes) with wr := s₂.wr.tail }

theorem wp_frame {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freedF s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freedF s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem zext8 (b : Byte) : BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The modulus' first byte. -/
theorem n0_ok {s t : State} (hp : SPre G s) (L : Lay t (fb s) (stackArg s 13)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 13) V W) (h18 : W 18 = s.gpr .rdx) (hrd : t.rd = s.rd)
    (hf : Frame (wrR s) s.mem t.mem) :
    WP isa (.block n0) t fun t' => Keep [.rsi, .rax] t t' ∧ t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0)) := by
  have hk1 := hp.k1
  have hn : t.mem (s.gpr .rdx) = s.mem (s.gpr .rdx) := by
    have := hf.bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) (in_apart hp.dKn hp.dOn hp.dns) (by dsimp only; have := hp.wN; omega_arith)
      (i := 0) (by dsimp only; omega_arith)
    simpa using this
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdx) 1 :=
    ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdx)).isLt; omega_arith)]
  exact ⟨rfl, rfl⟩

theorem restore_ok {s t : State} (hp : SPre G s) (D : SDone G s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (signK G).post s (freedF t') ∧
      (freedF t').mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hF := fb_toNat hp
  refine WP.mono_mx (by decide) (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ hmx => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_, by show t'.mxcsr.extractLsb' 6 10 = _; rw [hmx]; exact D.mx⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · show Spec.Rsa.writtenOutcome t'.mem _ _ ((t'.gpr .rax).setWidth 32) _
    rw [hm, k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    exact D.out

end VG.Proof.RsaPss.X86_64
