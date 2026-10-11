import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! Public layout and indices determine all row addresses and loop decisions. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)
open VG.Proof.MlKem.X86_64 (Keep)

structure RowLayout where
  B : Addr
  Z : Nat
  w : Nat
  i : Nat
  j₀ : Nat
  n : Nat
  hZ : slot w 8 ≤ Z
  hw : w < 2^31
  hi : i+8 ≤ w
  hwN : w = j₀+8*n
  hn : 0 < n

/-- Before column block `k`; the header slots `ps` hold the operands' bases. -/
def RowState (ps : List (Nat × Nat)) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12) = BitVec.ofNat 64 L.i ∧
    word s.mem L.B (8*sFn 13) = BitVec.ofNat 64 (L.j₀+8*k)

/-- At column block `k`, with the loop's state from a start `s₀` whose
memory has the operands' bases. -/
def LoopState (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ s₀ mi, Ops s₀.mem L.B L.w ps ∧ StreamInv s₀ L.B L.Z L.w a b L.i L.j₀ k mi s

def AtLoop (ps : List (Nat × Nat)) (a b : Nat) (p : RowLayout × Nat) (s : State) : Prop :=
  p.2 < p.1.n ∧ LoopState ps a b p.1 p.2 s

/-- After `setup`: the operands and the output at the row's first column block. -/
def RowBases (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (s : State) : Prop :=
  (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12) = BitVec.ofNat 64 L.i ∧
    word s.mem L.B (8*sFn 13) = BitVec.ofNat 64 L.j₀ ∧ word s.mem L.B carryOffset = 0 ∧
    s.gpr .rcx = off L.B (slot L.w a+8*L.i) ∧
    s.gpr .rbp = off L.B (slot L.w b+8*L.j₀) ∧
    s.gpr .rsi = off L.B (slot L.w aAcc+16+8*(L.i+L.j₀))

def RowRdi (p : RowLayout × Nat) (s : State) : Prop := s.gpr .rdi = p.1.B

theorem setup_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (L : RowLayout) (s : State) (h : RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) :
    WP isa (.block (AdxRect8.setup ca cb)) s (RowBases ps a b L) := by
  obtain ⟨⟨mi,hg,hv,hI,hJ⟩,hc⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at hJ
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr L.hZ hv pa pb hI hJ)
    fun t ⟨ca,cb,co,mt,kt⟩ => ?_
  exact ⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv,mt ▸ hI,mt ▸ hJ,
    mt ▸ hc,ca,cb,co⟩

theorem load_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : RowBases ps a b L s) :
    WP isa (.block AdxRotate8.loadCols) s (LoopState ps a b L 0) := by
  obtain ⟨⟨mi,hg⟩,hv,hI,hJ,hc,ca,cb,co⟩ := h
  have hwN := L.hwN; have hn := L.hn
  exact WP.mono (rowLoad_ok (s₀ := s) hg.scr hg.rdi hg.hdr L.hZ L.hi (by omega) hI hJ (by rw [hc]; rfl)
    ca cb co rfl (Keep.refl _ _)) fun t ht => ⟨s,mi,hv,ht⟩

theorem tile_fw {ps : List (Nat × Nat)} {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (p : RowLayout × Nat) (s : State) (h : AtLoop ps a b p s) :
    WP isa AdxRect8.streamTile s (RowRdi p) := by
  obtain ⟨hk,s₀,mi,_,h⟩ := h
  have hi := p.1.hi; have hwN := p.1.hwN; have hZ := p.1.hZ
  have nowrap := h.scr.nowrap
  have hj : p.1.j₀+8*p.2+8 ≤ p.1.w := by omega
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  have po : s.gpr .rsi = off p.1.B (slot p.1.w aAcc+16+8*(p.1.i+(p.1.j₀+8*p.2))) := by
    rw [h.po]; exact congrArg (off p.1.B) (by unfold rawBase; omega)
  refine WP.mono (streamTile_ok h.scr h.rdi h.pa h.pb po (by omega) (by omega) (by omega)
    ar.2.2 (by omega) (by unfold carryOffset sFn slot hdrBytes aAcc; omega))
    fun t ⟨_,_,_,_,_,_,kt⟩ => (kt.gpr (by decide)).trans h.rdi

theorem loop_pins (ps : List (Nat × Nat)) (a b : Nat) :
    Pins (AtLoop ps a b) [.rdi,.rcx,.rbp,.rsi] := by
  rintro p s t ⟨_,_,_,_,hs⟩ ⟨_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.rdi.trans ht.rdi.symm
  · exact hs.pa.trans ht.pa.symm
  · exact hs.pb.trans ht.pb.symm
  · exact hs.po.trans ht.po.symm

theorem row_body_ct {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    RelCT isa (Two (AtLoop ps a b)) AdxRect8.rowStep (fun _ _ => True) := by
  unfold AdxRect8.rowStep
  refine RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (loop_pins ps a b) (by taint_decide)
      (tile_fw ha hb ha1 ha2 hb1 hb2)) (two_taint [.rdi] ?_ (by taint_decide))
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.trans ht.symm

theorem row_fw {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (L : RowLayout) (k : Nat) (s : State) (hk : k < L.n) (h : LoopState ps a b L k s) :
    WP isa AdxRect8.rowStep s fun t =>
      isa.eval .ne t = some (decide (k+1 < L.n)) ∧
      (k+1 < L.n → LoopState ps a b L (k+1) t) ∧ (k+1 = L.n → LoopState ps a b L L.n t) := by
  obtain ⟨s₀,mi,hv,h⟩ := h
  refine WP.mono (streamStep_inv L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2 L.hwN hk h) fun t ⟨zt,ht⟩ => ?_
  have post : LoopState ps a b L (k+1) t := ⟨s₀,mi,hv,ht⟩
  refine ⟨?_,fun _ => post,fun he => he ▸ post⟩
  simp only [eval,zt,Option.map_some]
  by_cases he : k+1 = L.n
  · simp only [he,decide_true,Bool.not_true,show ¬(L.n<L.n) by omega,decide_false]
  · simp only [he,decide_false,Bool.not_false,show k+1<L.n by omega,decide_true]

theorem end_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : LoopState ps a b L L.n s) :
    WP isa (.block AdxRotate8.storeCols) s (RowState ps L L.n) := by
  obtain ⟨s₀,mi,hv,h⟩ := h
  refine WP.mono (rowEnd_ok L.hZ L.hi L.hwN h) fun t ht => ?_
  exact ⟨mi,⟨ht.scr,ht.rdi,ht.hdr⟩,frame_ops hv (by unfold rawBase slot; omega) ht.frame,ht.indexI,ht.indexJ⟩

theorem row_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two fun L s => RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) (AdxRect8.row ca cb)
      (Two fun L s => RowState ps L L.n s) := by
  unfold AdxRect8.row
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_fw pa pb)) ?_
  · rintro L s t ⟨⟨mi,hs,_⟩,_⟩ ⟨⟨mj,ht,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_piece [.rsi] ?_ (by taint_decide) load_fw) ?_
  · rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm
  refine RelCT.seq ((two_loop (fun L : RowLayout => L.n) (Φ := LoopState ps a b)
    (Ψ := fun L s => LoopState ps a b L L.n s)
    (row_body_ct ha hb ha1 ha2 hb1 hb2) (row_fw ha hb ha1 ha2 hb1 hb2)).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨L,hs,ht⟩
    exact ⟨L,⟨L.hn,hs⟩,L.hn,ht⟩
  refine two_post (two_taint [.rsi] ?_ (by taint_decide)) end_fw
  rintro L s t ⟨_,_,_,hs⟩ ⟨_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.po.trans ht.po.symm

end VG.Proof.Bignum.X86_64.AdxRect8
