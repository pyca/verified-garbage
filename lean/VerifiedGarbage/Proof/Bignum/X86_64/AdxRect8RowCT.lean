import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8CT

/-! Public layout and indices determine all row addresses and loop decisions. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

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

def AtRow (ps : List (Nat × Nat)) (p : RowLayout × Nat) (s : State) : Prop := p.2 < p.1.n ∧ RowState ps p.1 p.2 s

def RowBases (a b : Nat) (p : RowLayout × Nat) (s : State) : Prop :=
  p.2 < p.1.n ∧ (∃ mi, Good s p.1.B p.1.Z p.1.w mi) ∧
    s.gpr .rcx = off p.1.B (slot p.1.w a+8*p.1.i) ∧
    s.gpr .rbp = off p.1.B (slot p.1.w b+8*(p.1.j₀+8*p.2)) ∧
    s.gpr .rsi = off p.1.B (slot p.1.w aAcc+16+8*(p.1.i+(p.1.j₀+8*p.2)))

def RowRdi (p : RowLayout × Nat) (s : State) : Prop := s.gpr .rdi = p.1.B

theorem setup_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (p : RowLayout × Nat) (s : State) (h : AtRow ps p s) :
    WP isa (.block (AdxRect8.setup ca cb)) s (RowBases a b p) := by
  obtain ⟨hk,mi,hg,hv,hI,hJ⟩ := h
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr p.1.hZ hv pa pb hI hJ)
    fun t ⟨ca,cb,co,mt,kt⟩ => ?_
  exact ⟨hk,⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,ca,cb,co⟩

theorem tile_fw {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (p : RowLayout × Nat) (s : State) (h : RowBases a b p s) :
    WP isa AdxRect8.tile s (RowRdi p) := by
  obtain ⟨hk,⟨mi,hg⟩,ca,cb,co⟩ := h
  have hi := p.1.hi; have hwN := p.1.hwN; have hZ := p.1.hZ
  have hj : p.1.j₀+8*p.2+8 ≤ p.1.w := by omega
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  refine WP.mono (tile_ok hg.scr hg.rdi ca cb co (by omega) (by omega) (by omega)
    ar.2.2 (by omega) (by unfold carryOffset sFn slot hdrBytes aAcc; omega))
    fun t ⟨_,_,_,_,_,kt⟩ => (kt.gpr (by decide)).trans hg.rdi

theorem row_body_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two (AtRow ps)) (AdxRect8.rowStep ca cb) (fun _ _ => True) := by
  unfold AdxRect8.rowStep AdxRect8.tileAt
  refine RelCT.seq (RelCT.seq (two_piece [.rdi] ?_ hS (setup_fw pa pb))
    (two_piece [.rdi,.rcx,.rbp,.rsi] ?_ (by taint_decide)
      (tile_fw ha hb ha1 ha2 hb1 hb2))) (two_taint [.rdi] ?_ (by taint_decide))
  · rintro p s t ⟨_,mi,hs,_,_,_⟩ ⟨_,mj,ht,_,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro p s t ⟨_,⟨mi,hs⟩,caS,cbS,coS⟩ ⟨_,⟨mj,ht⟩,caT,cbT,coT⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.rdi.trans ht.rdi.symm
    · exact caS.trans caT.symm
    · exact cbS.trans cbT.symm
    · exact coS.trans coT.symm
  · intro p s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

theorem row_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (L : RowLayout) (k : Nat) (s : State) (hk : k < L.n) (h : RowState ps L k s) :
    WP isa (AdxRect8.rowStep ca cb) s fun t =>
      isa.eval .ne t = some (decide (k+1 < L.n)) ∧
      (k+1 < L.n → RowState ps L (k+1) t) ∧ (k+1 = L.n → RowState ps L L.n t) := by
  obtain ⟨mi,hg,hv,hI,hJ⟩ := h
  have hwN := L.hwN
  refine WP.mono (rowStep_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hi (by omega) hv pa pb
    ha hb ha1 ha2 hb1 hb2 hI hJ) fun t ⟨zt,jt,_,_,_,ht,ft,_,kt⟩ => ?_
  have it : word t.mem L.B (8*sFn 12) = BitVec.ofNat 64 L.i := by
    rw [ft.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        simp only [carryOffset,sFn,slot,hdrBytes,aAcc] <;> omega) (by decide)]
    exact hI
  have post : RowState ps L (k+1) t :=
    ⟨mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩,
      frame_ops hv (by unfold slot; omega) ft,it,
      by simpa only [show L.j₀+8*(k+1)=(L.j₀+8*k)+8 by omega] using jt⟩
  refine ⟨?_,fun _ => post,fun he => he ▸ post⟩
  simp only [eval,zt,Option.map_some]
  by_cases he : k+1 = L.n
  · simp only [show L.j₀+8*k+8=L.w by omega,decide_true,Bool.not_true,
      show ¬(k+1<L.n) by omega,decide_false]
  · simp only [show ¬(L.j₀+8*k+8=L.w) by omega,decide_false,Bool.not_false,
      show k+1<L.n by omega,decide_true]

theorem row_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two fun L s => RowState ps L 0 s) (AdxRect8.row ca cb)
      (Two fun L s => RowState ps L L.n s) := by
  unfold AdxRect8.row
  refine (two_loop (fun L : RowLayout => L.n) (Φ := RowState ps)
    (row_body_ct pa pb ha hb ha1 ha2 hb1 hb2 hS) (row_fw pa pb ha hb ha1 ha2 hb1 hb2)).mono ?_ (fun _ _ h => h)
  rintro s t ⟨L,hs,ht⟩
  exact ⟨L,⟨L.hn,hs⟩,L.hn,ht⟩

end VG.Proof.Bignum.X86_64.AdxRect8
