import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8

/-! A rectangular tile adds one full 1024-bit product and a high-half carry. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem upper_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hp : s.gpr .rsi = off B e)
    (he : carryOffset + 8 ≤ Z) :
    WP isa (.block AdxRect8.upper) s fun t =>
      t.gpr .rdx = word s.mem B carryOffset ∧ t.gpr .rsi = off B (e+64) ∧
      t.mem = s.mem ∧ Keep [.rdx,.rsi] s t := by
  refine WP.mono (WP.keep [.rdx,.rsi] (Q := fun t =>
    t.gpr .rdx = word s.mem B carryOffset ∧ t.gpr .rsi = off B (e+64) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b,c⟩,k⟩ => ⟨a,b,c,k⟩
  unfold AdxRect8.upper
  have load := hs.ld he
  change InRegions (s.rd ++ s.wr) (off B (8*sFn 14)) 8 at load
  xrun [State.ea,hdr,hd,hdrOff,hp,load,
    show (64 : BitVec 32).signExtend 64 = 64 from rfl]
  simp only [carryOffset,off,BitVec.ofNat_add,BitVec.add_assoc]
  exact ⟨True.intro,rfl⟩

theorem tile_ok {s : State} {B : Addr} {Z eA eB eO : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (ha : s.gpr .rcx = off B eA)
    (hb : s.gpr .rbp = off B eB) (ho : s.gpr .rsi = off B eO)
    (hA : eA + 64 ≤ Z) (hB : eB + 64 ≤ Z) (hO : eO + 128 ≤ Z)
    (sepA : eA + 64 ≤ eO ∨ eO + 128 ≤ eA)
    (sepB : eB + 64 ≤ eO ∨ eO + 128 ≤ eB)
    (sepC : carryOffset + 8 ≤ eO) :
    WP isa AdxRect8.tile s fun t =>
      wv t.mem B eO 16 + 2^1024 * (word t.mem B carryOffset).toNat =
        wv s.mem B eO 16 + wv s.mem B eA 8 * wv s.mem B eB 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Frm B [(eO,128),(carryOffset,8)] s.mem t.mem ∧ t.gpr .rsi = off B (eO+64) ∧
      Keep [.rdx,.rax,.rbx,.rsi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxRect8.tile
  refine WP.seq (WP.mono (product_ok hs ha hb ho hA hB (by omega) (by omega) (by omega))
    fun a ⟨ea,oa,ka⟩ => ?_)
  refine WP.seq (WP.mono (upper_ok (hs.congr ka.2.2)
    ((ka.gpr (by decide)).trans hd) ((ka.gpr (by decide)).trans ho) (by omega))
    fun b ⟨db,pb,mb,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.seq (WP.mono (finish_ok (hs.congr kab.2.2) pb (by omega))
    fun c ⟨ec,bc,oc,kc⟩ => ?_)
  have kabc := kab.trans kc
  have address : c.ea (hdr (sFn 14)) = off B carryOffset := by
    simp only [State.ea,hdr,(kabc.gpr (by decide)).trans hd,hdrOff,carryOffset]
  refine WP.mono (storeMem_ok (hs.congr kabc.2.2) address (by omega))
    fun t ⟨wt,ot,kt⟩ => ?_
  have carryA : word a.mem B carryOffset = word s.mem B carryOffset :=
    oa.word (by omega) (by have := hs.nowrap; omega)
  have upperA : wv a.mem B (eO+64) 8 = wv s.mem B (eO+64) 8 :=
    oa.wv (by omega) (by have := hs.nowrap; omega)
  have lowC : wv c.mem B eO 8 = wv a.mem B eO 8 := by
    rw [oc.wv (by omega) (by have := hs.nowrap; omega),mb]
  have allT : wv t.mem B eO 16 = wv c.mem B eO 16 :=
    ot.wv (by omega) (by have := hs.nowrap; omega)
  rw [cols_keep kb (by decide),mb,db,carryA,upperA] at ec
  refine ⟨?_,?_,?_,?_,?_,(kabc.trans kt).mono (by decide)⟩
  · rw [allT,wt,show 16 = 8+8 from rfl,wv_add,wv_add]
    simp only [Nat.reduceMul] at *
    rw [lowC]
    omega_using [ea,ec]
  · rw [wt]; exact bc
  · intro cin
    rw [wt]
    have ca := cols_lt a
    have hi := wv_lt s.mem B (eO+64) 8
    simp only [Nat.reduceMul] at hi
    omega_using [ec,ca,hi,cin]
  · have ab : Outside B eO 128 s.mem c.mem :=
      (oa.mono (o' := eO) (n' := 128) (by omega) (by omega)).trans (by
        rw [mb] at oc
        exact oc.mono (o' := eO) (n' := 128) (by omega) (by omega))
    exact (Frm.of_outside ab (by simp)).trans (Frm.of_outside ot (by simp))

  · exact (kt.gpr (by simp)).trans ((kc.gpr (by decide)).trans pb)

end VG.Proof.Bignum.X86_64.AdxRect8
