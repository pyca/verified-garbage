module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Batteries.Logic
public import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Lit

/-! ### `RsaPss.X86_64.SignFail`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on x86-64: refusing

`signFail` writes zeros to `out` and returns 0 (`signFail_ok`), changing
nothing else of the working space or the frame.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

/-- `Rep` across changes outside the working space and the frame. -/
theorem Rep.of_outside {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    {O : Region} (hm : ∀ x, ¬ O.Contains x 1 → m' x = m x) (hS : O.Disjoint ⟨S, oRsa⟩)
    (hF : O.Disjoint ⟨F, frameBytes⟩) (G : Geo F S) : Rep m' F S V W where
  scr o ho := by
    rw [hm _ fun h => hS _ h (Offset.contains_base _ (by omega_using [ho]) (by unfold oRsa at *; omega_using [ho])), R.scr o ho]
  fr k hk := by
    rw [← R.fr k hk]
    refine Mem.readW_congr fun i hi => hm _ fun h => hF _ h ?_
    have := G.Fw
    rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk, hi]) (by unfold nW frameBytes at *; omega_using [hk, hi])

structure ZI (u₀ : State) (p : Addr) (j : Nat) (v : State) : Prop where
  keep : Keep [.r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  mem : ∀ x, v.mem x = if (⟨p, j⟩ : Region).Contains x 1 then 0 else u₀.mem x

/-- Zeros to the `n` bytes at `p` (`rdi`), a byte at a time. -/
theorem zeroOut_ok {u₀ : State} {p : Addr} {n : Nat} {cnt : Src} (hs : StepOk cnt n u₀ [.r8]) (hn : 0 < n)
    (hpn : p.toNat + n ≤ 2 ^ 64) (hw : (⟨p, n⟩ : Region) ∈ u₀.wr)
    (hdi : u₀.gpr .rdi = p) (hax : u₀.gpr .rax = 0) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.store8 (ix .rdi .r8) .rax] cnt) u₀ fun u' => Keep [.r8] u₀ u' ∧
      ∀ x, u'.mem x = if (⟨p, n⟩ : Region).Contains x 1 then 0 else u₀.mem x := by
  refine WP.mono (byteLoop_ok hn hs (ZI u₀ p) ?_ (u := u₀)
    ⟨Keep.refl _ _, h8, fun x => by simp [Region.Contains]⟩) fun u' I => ⟨I.keep, I.mem⟩
  intro j hj v I
  have hdv : v.gpr .rdi = p := (I.keep.gpr (by decide)).trans hdi
  have hav : v.gpr .rax = 0 := (I.keep.gpr (by decide)).trans hax
  have hea : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 j := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hin : InRegions v.wr (p + BitVec.ofNat 64 j) 1 :=
    ⟨_, I.keep.2.2 ▸ hw, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hpn, hj])⟩
  refine WP.mono (WP.keep [] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (p + BitVec.ofNat 64 j) (0 : Byte)) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hdv, I.r8, hea, hin, hav]
    rfl
  refine ⟨(I.keep.trans (k.trans k')).mono (by decide), h8'', fun x => ?_⟩
  rw [hm', hm, VG.WriteBytes.writeW8_apply, I.mem x]
  have hx : (x - p).toNat < 2 ^ 64 := (x - p).isLt
  by_cases he : x = p + BitVec.ofNat 64 j
  · subst he
    rw [ifp rfl]
    exact (ifp (show (⟨p, j + 1⟩ : Region).Contains (p + BitVec.ofNat 64 j) 1 from
      Offset.contains_base _ (by omega_using []) (by omega_using [hpn, hj])) _ _).symm
  · rw [ifn he]
    have hne : (x - p).toNat ≠ j := fun h => he (by
      rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
    have iff : (⟨p, j + 1⟩ : Region).Contains x 1 ↔ (⟨p, j⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]; omega_using [hne]
    by_cases h1 : (⟨p, j⟩ : Region).Contains x 1
    · rw [ifp h1, ifp (iff.mpr h1)]
    · rw [ifn h1, ifn (fun h => h1 (iff.mp h))]

/-- Zeros to `out` (`k` bytes) and 0 in `rax`. -/
theorem signFail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {out : Addr} {k : Nat} (ho : W 16 = out) (hk : W 17 = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hw : (⟨out, k⟩ : Region) ∈ u.wr) (hpn : out.toNat + k ≤ 2 ^ 64)
    (hS : (⟨out, k⟩ : Region).Disjoint ⟨S, oRsa⟩) (hF : (⟨out, k⟩ : Region).Disjoint ⟨F, frameBytes⟩) :
    WP isa signFail u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      u'.gpr .rax = 0 ∧ Spec.Rsa.bytesAt u'.mem out k = List.replicate k 0 ∧
      (∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → u'.mem x = u.mem x) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rax, .r8] (Q := fun v => v.gpr .rdi = out ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [signFail, ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.rd (d := sOut) 16 rfl (by decide), R.rd (d := sK) 17 rfl (by decide), ho, hk]
  refine WP.mono (zeroOut_ok (stepR_ok (by omega_using [hk2]) v (show Reg.r10 ∉ [Reg.r8] by decide) (by decide) h₁₀)
    (by omega_using [hk1]) hpn (by rw [hkv.2.2]; exact hw) h₁ h₂ h₃) fun w ⟨kw, hmw⟩ => ?_
  have hout : ∀ x, ¬ (⟨out, k⟩ : Region).Contains x 1 → w.mem x = u.mem x := fun x hx => by
    rw [hmw, ifn hx, hm]
  have Rw : Rep w.mem F S V W := R.of_outside hout hS hF L.geo
  refine ⟨L.of_rep R Rw ((kw.gpr (by decide)).trans (hkv.gpr (by decide))) (kw.2.2.trans hkv.2.2),
    (hkv.trans kw).mono (by decide), Rw, (kw.gpr (by decide)).trans h₂, ?_, hout⟩
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [hmw, ifp (Offset.contains_base _ (by simp at h₁; omega_using [h₁]) (by simp at h₁; omega_using [hk2, h₁]))]

end VG.Proof.RsaPss.X86_64

end

end

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

variable {tsH tsG : List FnTable}

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
theorem frame_keep {s u v : State} (hp : SPre tsH tsG s) (hw : u.wr = frR s :: s.wr) (hsp : u.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem u.mem)
    (hk : ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 16).Contains a 1 → v.mem a = u.mem a) :
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

/-- The outcome `signK.post` asks for, with the hash functions `H` and `G`
the tables name. -/
def signOut (H G : Spec.Mgf1.Hash) (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat)

/-- Before the epilogue: the outcome written, the saved registers in their
slots. -/
structure SDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 14)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G →
    Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (signOut H G s)
  /-- MXCSR's control bits. -/
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem fail_done {s t : State} (hp : SPre tsH tsG s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t (fb s) (stackArg s 14)) (R : Rep t.mem (fb s) (stackArg s 14) V W) (hw : t.wr = frR s :: s.wr)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12) (hinv : ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some G → signOut H G s = .invalid)
    (hmx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) :
    WP isa signFail t (SDone s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [hw, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  refine WP.mono_mx (by decide) (signFail_ok L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) h16
    (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2 hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun t' ⟨L', k', R', hax, hz, _⟩ hm => ?_
  refine ⟨L', k'.2.2.trans hw, fun r hr => (k'.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide)).trans
    (hcs r hr), ?_, ?_, ?_, ?_, by rw [hm]; exact hmx⟩
  · rw [R'.rd (d := sRbx) 41 rfl (by decide), h41]
  · rw [R'.rd (d := sRbp) 42 rfl (by decide), h42]
  · rw [R'.rd (d := sR12) 43 rfl (by decide), h43]
  · intro H G hH hG; rw [hinv H G hH hG]; exact ⟨by rw [hax]; rfl, hz⟩

/-- Stack arguments, kept where the function does not write. -/
theorem argsKept_of {s : State} (hp : SPre tsH tsG s) {m : Mem} (hM : Frame (wrR s) s.mem m) : ArgsKept s m := by
  intro j hj
  refine hM.readW (r := ⟨stackArgAddr s 0, 144⟩) ?_ (in_apart hp.dKa hp.dOa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith]
  have := hp.sp2
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

/-- The state after the frame's pop. -/
def freedF (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 frameBytes) with wr := s₂.wr.tail }

/-- The frame, whose bytes hold whatever they hold once released (`alloc_frame_ok`). -/
theorem wp_frame {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ ∀ m u, Frame [⟨fb s, frameBytes⟩] s₂.mem m →
        Q { freedF s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q :=
  alloc_frame_ok (by decide) hsp hb

theorem zext8 (b : Byte) : BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The modulus' first byte. -/
theorem n0_ok {s t : State} (hp : SPre tsH tsG s) (L : Lay t (fb s) (stackArg s 14)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 14) V W) (h18 : W 18 = s.gpr .rdx) (hrd : t.rd = s.rd)
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
    ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, hp.rdIn hrd (by simp), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rdx)).toNat ∧
      t'.zf = some (decide ((s.mem (s.gpr .rdx)).toNat = 0))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, ea_at0, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 18 rfl (by decide), h18, hin, hn]
  rw [zext8, BitVec.and_self, ofNat_beq_zero (by have := (s.mem (s.gpr .rdx)).isLt; omega_arith)]
  exact ⟨rfl, rfl⟩

theorem restore_ok {s t : State} (hp : SPre tsH tsG s) (D : SDone s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      ∀ m u, Frame [⟨fb s, frameBytes⟩] t'.mem m →
        (∀ r ∈ calleeSaved, ({ freedF t' with mem := m, unknowns := u } : State).gpr r = s.gpr r) ∧ (signK tsH tsG).post s ({ freedF t' with mem := m, unknowns := u } : State) ∧
        ({ freedF t' with mem := m, unknowns := u } : State).mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hF := fb_toNat hp
  refine WP.mono_mx (by decide) (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ hmx => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun m u fm => ⟨fun r hr => ?_, ?_,
    by show t'.mxcsr.extractLsb' 6 10 = _; rw [hmx]; exact D.mx⟩⟩
  · show (freedF t').gpr r = s.gpr r
    simp only [freedF, State.setReg]
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
  · intro H G hH hG
    show Spec.Rsa.writtenOutcome m _ _ ((t'.gpr .rax).setWidth 32) _
    have hsi := hp.hsi
    refine Proof.Rsa.writtenOutcome_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.dKo.sub_left (frame_sub s)).symm
      rwa [hsi] at this) ?_
    rw [hm, k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    exact D.out H G hH hG

end VG.Proof.RsaPss.X86_64
