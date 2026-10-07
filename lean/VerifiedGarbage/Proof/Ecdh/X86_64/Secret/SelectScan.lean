import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY

/-! Both table-scan backends select the same ten 16-byte pieces, including cached powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

private theorem selPassY_congr (o H st np : Nat) {q q' : Nat → Nat}
    (h : ∀ c<np,q c=q' c) : selPassY o H st np q=selPassY o H st np q' := by
  have he : ∀ m,selEntryY st np q m=selEntryY st np q' m := by
    intro m
    unfold selEntryY
    congr 1
    rw [List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro c hc
    rw [h c (List.mem_range.mp hc)]
  unfold selPassY
  simp only [he]
  congr 2
  apply List.map_congr_left
  intro c hc
  rw [h c (List.mem_range.mp hc)]

/-- `M.n` counts 16-byte scan pieces here; no field arithmetic uses this configuration. -/
private abbrev scanCfg (K : WinCfg) : TCombCfg :=
  {WinCfg.tc K with M := {K.M with n := 10},w := 5,avx2 := K.M.adx}

private theorem scanCfg_code (K : WinCfg) : (scanCfg K).selPassV=
    if K.M.adx then selPassY K.E.x 16 160 5 (2*·) else selPassAt K.E.x 16 160 10 (16*·) := by
  simp only [TCombCfg.selPassV,TCombCfg.H,WinCfg.tc,TCombCfg.selPass]
  simp only [Nat.reduceSub,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceDiv]
  rw [selPassY_congr K.E.x 16 160 5 (q':=(2*·)) (by
    intro c hc
    unfold qY
    split <;> omega)]
  cases K.M.adx <;> rfl

theorem select_scan_ok (K : WinCfg) {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ht : K.tbl<2^31) (hT : K.tbl+2560≤size)
    (hE : K.E.x+160≤size) (ha : a≤16) (h8 : s.gpr .r8=BitVec.ofNat 64 a) :
    WP isa (.block (WinCfg.selSetup K ++
      (if K.M.adx then selPassY K.E.x 16 160 5 (2*·) else selPassAt K.E.x 16 160 10 (16*·)))) s fun t =>
      (∀ i<20,word t.mem base (K.E.x+8*i)=
        if 1≤a then word s.mem base (K.tbl+160*(a-1)+8*i) else 0) ∧
      Outside base K.E.x 160 s.mem t.mem ∧ KeepRegs [.rax,.rcx,.rdx] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (winSelSetup_ok K s hs.rdi ht) fun u ⟨xu,ku,_⟩ => ?_
  have hu := hs.of_keeps ku (by decide)
  have h8u : u.gpr .r8=BitVec.ofNat 64 a := (ku.1 _ (by decide)).trans h8
  have hreg : InRegions (u.rd++u.wr) (base+BitVec.ofNat 64 K.tbl) 2560 :=
    ⟨_,List.mem_append_right _ hu.wr,hu.contains hT (by decide)⟩
  have hr : ∀ e<16,∀ c<10,InRegions (u.rd++u.wr)
      (base+BitVec.ofNat 64 K.tbl+BitVec.ofNat 64 (160*e+16*c)) 16 := by
    intro e he c hc
    exact VG.CallLay.inRegions_sub hreg (by omega) (by decide)
  rw [←scanCfg_code]
  refine WP.mono (selPassV_ok (scanCfg K) hu (by change 10≤14; decide) (by change 16<2^31; decide) (by omega)
    h8u xu hr hreg (by change 2560<2^31; decide) hE) fun t ⟨vt,ot,kt⟩ => ?_
  refine ⟨?_,by rw [ku.2.1] at ot; exact ot,
    (VG.Proof.Mont.X86_64.Keeps.regs ku).mono (by decide) |>.trans (kt.mono (by decide))⟩
  intro i hi
  have vv := vt (i/2) (by change i/2<10; omega)
  change t.mem.readW (off base (K.E.x+16*(i/2))) 128=
    accVal u.mem (base+BitVec.ofNat 64 K.tbl) 160 (16*·) a 16 (i/2) at vv
  rw [ku.2.1] at vv
  have hw := accVal_word1 (q:=i%2) vv (Nat.mod_lt _ (by decide))
  have he : K.E.x+16*(i/2)+8*(i%2)=K.E.x+8*i := by omega
  have hx : ∀ d,word s.mem (base+BitVec.ofNat 64 K.tbl) d=word s.mem base (K.tbl+d) := by
    intro d
    rw [Mont.word,Mont.word,off,off,Offset.add_add]
  rw [he,hx,show K.tbl+(160*(a-1)+16*(i/2)+8*(i%2))=K.tbl+160*(a-1)+8*i by omega] at hw
  simpa only [show (1≤a ∧ a≤16) ↔ 1≤a by omega] using hw

end VG.Proof.Ecdh.X86_64.Secret
