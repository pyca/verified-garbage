import VerifiedGarbage.Proof.Weierstrass.X86.Window

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

theorem selPtInplace_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0)) {n : Nat} {o b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, o.x, o.y, o.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o o b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base o.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base o.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base o.z n) ∧
      Keeps [.eax, .edx] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xbx, xby, xbz⟩, ⟨ybx, yby, ybz⟩, ⟨zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs hc (by omega_using [iox]) (by omega_using [iax]) (by omega_using [ibx])
    (Or.inl (Nat.le_refl _)) (by omega_using [xbx])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c (2 * n) hs₁ (by rw [k₁.1 _ (by decide), hc]) (by omega_using [ioy])
    (by omega_using [iay]) (by omega_using [iby]) (Or.inl (Nat.le_refl _)) (by omega_using [yby]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (sel_ok c (2 * n) hs₂ (by rw [k₂.1 _ (by decide), k₁.1 _ (by decide), hc])
    (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [ibz]) (Or.inl (Nat.le_refl _))
    (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.val32 (d := o.y) (by omega_using [xy]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.val32 (d := o.z) (by omega_using [yz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.val32 (d := o.z) (by omega_using [xz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))


theorem winE_mem {K : WinCfg} : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> win_mem

def entryW (K : WinCfg) : List (Nat × Nat) :=
  [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)]

theorem entryW_sub (K : WinCfg) : ∀ w ∈ entryW K, w ∈ winW K := by
  intro w hw
  simp only [entryW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;>
    exact List.mem_append_left _ (List.mem_map_of_mem (winOther_ws K _ (winE_mem _ (by simp))))

theorem entry_table_unch {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {m m' : Mem} (hU : Unch base (entryW K) m m') (hn : base.toNat + size ≤ 2 ^ 32)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 8) :
    ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  intro x hx
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hj.1 hj.2 x hx
  refine hU.wordsVal (fun w hw => ?_) (by
    have := hL.lay.le _ (List.mem_append_right _ (winTbl_mem K hi)); omega)
  simp only [entryW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;>
    exact (hL.tbl_apart (List.mem_append_right _ (winE_mem _ (by simp))) hi).symm

/-- Scan one point in place; the table and the public counter survive. -/
theorem selectOne_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) {j a : Nat} (hj : 1 ≤ j ∧ j ≤ 8)
    (ha : a ≤ 8) (hb : s.gpr .ebx = BitVec.ofNat 32 a) :
    WP isa (.block (eqMask j ++ selPt K.M.n K.E K.E (K.tblPt j))) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if a = j then wordsVal s.mem base (K.tblPt j).x K.M.n else wordsVal s.mem base K.E.x K.M.n) ∧
      wordsVal t.mem base K.E.y K.M.n = (if a = j then wordsVal s.mem base (K.tblPt j).y K.M.n else wordsVal s.mem base K.E.y K.M.n) ∧
      wordsVal t.mem base K.E.z K.M.n = (if a = j then wordsVal s.mem base (K.tblPt j).z K.M.n else wordsVal s.mem base K.E.z K.M.n) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Unch base (entryW K) s.mem t.mem := by
  have eS : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winWs K := by
    intro x hx; exact winOther_ws K _ (winE_mem _ (List.mem_append_left [K.neg] hx))
  have tS := tblPt_slots K hj.1 hj.2
  have leE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x + 8 * K.M.n ≤ size :=
    fun x hx => hL.lay.le _ (winWs_slots K _ (eS x hx))
  have apart : ∀ x ∈ [K.E.x, K.E.y, K.E.z],
      ∀ y ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hj.1 hj.2 y hy
    exact hL.tbl_apart (List.mem_append_right _ (winE_mem _ (List.mem_append_left [K.neg] hx))) hi
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  refine WP.block_append (WP.mono (eqMask_ok s (by omega) (by omega) hb) fun s₁ ⟨mask,k₁,_⟩ => ?_)
  refine WP.mono (selPtInplace_ok (hs.of_keeps k₁.keeps (by decide)) (decide (a = j)) mask
    (o := K.E) (b := K.tblPt j) (n := K.M.n) ?_ ?_ apart) fun t ⟨x,y,z,k₂,U₂⟩ => ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with h | h | h | h | h | h | h | h | h
    · exact leE d (by simp [h])
    · exact leE d (by simp [h])
    · exact leE d (by simp [h])
    · exact leE d (by simp [h])
    · exact leE d (by simp [h])
    · exact leE d (by simp [h])
    · exact hL.lay.le _ (tS d (by simp [h])).1
    · exact hL.lay.le _ (tS d (by simp [h])).1
    · exact hL.lay.le _ (tS d (by simp [h])).1
  · exact ⟨hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) exy,
      hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) exz,
      hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) eyz⟩
  · simp only [decide_eq_true_eq, k₁.2.1] at x y z
    exact ⟨x,y,z,(k₁.keeps.mono (by decide)).trans (k₂.mono (by decide)),
      by rw [← k₁.2.1]; exact Outs.unch U₂⟩

/-- The first m entries, starting with the neutral point. -/
theorem selectEntries_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) {a : Nat} (ha : a ≤ 8)
    (hb : s.gpr .ebx = BitVec.ofNat 32 a)
    (hx : wordsVal s.mem base K.E.x K.M.n = 0)
    (hy : wordsVal s.mem base K.E.y K.M.n = K.one)
    (hz : wordsVal s.mem base K.E.z K.M.n = 0) :
    ∀ m ≤ 8, WP isa (.block (WinCfg.selectEntries K m)) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a ∧ a ≤ m then wordsVal s.mem base (K.tblPt a).x K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ a ∧ a ≤ m then wordsVal s.mem base (K.tblPt a).y K.M.n else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ a ∧ a ≤ m then wordsVal s.mem base (K.tblPt a).z K.M.n else 0) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Unch base (entryW K) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simpa only [show ¬ (1 ≤ a ∧ a ≤ 0) by omega, ↓reduceIte] using hx, by simpa only [show ¬ (1 ≤ a ∧ a ≤ 0) by omega, ↓reduceIte] using hy, by simpa only [show ¬ (1 ≤ a ∧ a ≤ 0) by omega, ↓reduceIte] using hz, Keeps.refl _ _, Unch.refl _ _ _⟩
  | m + 1, hm => by
    rw [WinCfg.selectEntries, List.append_assoc]
    refine WP.block_append (WP.mono (selectEntries_ok hL hs ha hb hx hy hz m (by omega))
      fun s₁ ⟨x₁,y₁,z₁,k₁,U₁⟩ => ?_)
    refine WP.mono (selectOne_ok hL (hs.of_keeps k₁ (by decide)) (j := m + 1) (by omega) ha
      (by rw [k₁.1 _ (by decide), hb])) fun t ⟨x₂,y₂,z₂,k₂,U₂⟩ => ?_
    have e := entry_table_unch hL U₁ hs.nowrap (j := m + 1) (by omega)
    refine ⟨?_,?_,?_,k₁.trans k₂,(U₁.trans U₂).mono (by intro w hw; rcases List.mem_append.mp hw with h | h <;> exact h)⟩
    all_goals
      first | rw [x₂, e _ (by simp), x₁] | rw [y₂, e _ (by simp), y₁] | rw [z₂, e _ (by simp), z₁]
      by_cases h : a = m + 1
      · subst a; simp
      · have hm' : (1 ≤ a ∧ a ≤ m + 1) ↔ (1 ≤ a ∧ a ≤ m) := by omega
        simp only [h, ↓reduceIte, hm']

structure WinSelPost (K : WinCfg) (base : Addr) (s : State) (a : Nat) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).x K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).y K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then wordsVal s.mem base (K.tblPt a).z K.M.n else 0
  keep : Keeps [.eax, .ecx, .edx] s t
  unch : Unch base (entryW K) s.mem t.mem

theorem winSelect_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) (hone : K.one < 2 ^ (64 * K.M.n))
    {a : Nat} (hb : s.gpr .ebx = BitVec.ofNat 32 a) (ha : a ≤ 8) :
    WP isa (.block (WinCfg.select K)) s (WinSelPost K base s a) := by
  have hn := hs.nowrap
  have eS : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ winWs K := by
    intro x hx; exact winOther_ws K _ (winE_mem _ (List.mem_append_left [K.neg] hx))
  have le : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x + 8 * K.M.n ≤ size :=
    fun x hx => hL.lay.le _ (winWs_slots K _ (eS x hx))
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  have xy := hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) exy
  have xz := hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) exz
  have yz := hL.apart₂ (eS _ (by simp)) (eS _ (by simp)) eyz
  rw [WinCfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (setConst_ok hs (le _ (by simp)) (Nat.two_pow_pos (64 * K.M.n)))
    fun s₁ ⟨x₁,k₁,O₁⟩ => ?_)
  refine WP.block_append (WP.mono (setConst_ok (hs.of_keeps k₁ (by decide)) (le _ (by simp)) hone)
    fun s₂ ⟨y₂,k₂,O₂⟩ => ?_)
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₂ (le _ (by simp)) (Nat.two_pow_pos (64 * K.M.n)))
    fun s₃ ⟨z₃,k₃,O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have K₃ := (k₁.trans k₂).trans k₃
  have U₃ : Unch base (entryW K) s.mem s₃.mem := O₁.unch.trans (O₂.unch.trans O₃.unch)
  have x₃ : wordsVal s₃.mem base K.E.x K.M.n = 0 := by
    rw [O₃.wordsVal (by omega) (by have := le _ (show K.E.x ∈ [K.E.x,K.E.y,K.E.z] by simp); omega),
      O₂.wordsVal (by omega) (by have := le _ (show K.E.x ∈ [K.E.x,K.E.y,K.E.z] by simp); omega),x₁]
  have y₃ : wordsVal s₃.mem base K.E.y K.M.n = K.one := by
    rw [O₃.wordsVal (by omega) (by have := le _ (show K.E.y ∈ [K.E.x,K.E.y,K.E.z] by simp); omega),y₂]
  refine WP.mono (selectEntries_ok hL hs₃ ha (by rw [K₃.1 _ (by decide),hb]) x₃ y₃ z₃ 8 (by decide))
    fun t ⟨x,y,z,k,U⟩ => ?_
  have value : ∀ d ∈ [(K.tblPt a).x,(K.tblPt a).y,(K.tblPt a).z], 1 ≤ a →
      wordsVal s₃.mem base d K.M.n = wordsVal s.mem base d K.M.n :=
    fun d hd h1 => entry_table_unch hL U₃ hn ⟨h1,ha⟩ d hd
  refine ⟨?_,?_,?_,(K₃.mono (by decide)).trans k,
    (U₃.trans U).mono (by intro w hw; rcases List.mem_append.mp hw with h | h <;> exact h)⟩
  all_goals
    first | rw [x] | rw [y] | rw [z]
    by_cases h1 : 1 ≤ a
    · simp only [h1,ha,and_self,↓reduceIte]; exact value _ (by simp) h1
    · simp only [h1,false_and,↓reduceIte]

end VG.Proof.Weierstrass.X86
