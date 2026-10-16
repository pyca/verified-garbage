module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledInit
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquare
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCarry8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Add
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! # The cross tile of a 16-word square

`AdxTiledSquare.cross16` adds `a[0..8) * a[8..16)` at word 8 of the raw
product: the tile's eight products, the next eight words added to its
columns in one carry chain, and that chain's carry through the eight words
above. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.Bignum.X86_64.AdxTiledProduct (ranges frame_hdr)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem init16_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxTiledSquare.init16) s fun t =>
      word t.mem B (8*sFn 12) = BitVec.ofNat 64 0 ∧ word t.mem B (8*sFn 13) = BitVec.ofNat 64 8 ∧
      Outside B (8*sFn 12) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have iZ : 8*sFn 12+8 ≤ Z := by have := hdr_lt_slot w 8 (show sFn 12 < 32 by decide); omega
  have jZ : 8*sFn 13+8 ≤ Z := by have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega
  have body : WP isa (.block AdxTiledSquare.init16) s fun t =>
      t.mem = (s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 0)).writeW (off B (8*sFn 13)) (BitVec.ofNat 64 8) ∧
        Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem =
      (s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 0)).writeW (off B (8*sFn 13)) (BitVec.ofNat 64 8)) _ rfl
    unfold AdxTiledSquare.init16
    xrun [State.ea,hdr,hd,hdrOff,hs.st iZ,hs.st jZ]
    rfl
  refine WP.mono body fun t ⟨mt,kt⟩ => ?_
  have c := writeW_outside s.mem B (BitVec.ofNat 64 0) (by omega : 8*sFn 12+8 ≤ 2^64)
  have j := writeW_outside (s.mem.writeW (off B (8*sFn 12)) (BitVec.ofNat 64 0)) B (BitVec.ofNat 64 8)
    (by omega : 8*sFn 13+8 ≤ 2^64)
  refine ⟨?_,?_,?_,kt⟩
  · rw [mt,j.word (by unfold sFn; omega) (by omega),word_writeW_self]
  · rw [mt,word_writeW_self]
  · rw [mt]
    exact (c.mono (o' := 8*sFn 12) (n' := 16) (by omega) (by unfold sFn; omega)).trans
      (j.mono (o' := 8*sFn 12) (n' := 16) (by unfold sFn; omega) (by unfold sFn; omega))

theorem addRsi_ok {s : State} {B : Addr} {e : Nat} (hp : s.gpr .rsi = off B e) :
    WP isa (.block [.alu .add .rsi (.imm 64)]) s fun t =>
      t.gpr .rsi = off B (e+64) ∧ t.mem = s.mem ∧ Keep [.rsi] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (e+64) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b⟩,k⟩ => ⟨a,b,k⟩
  xrun [hp,show (64 : BitVec 32).signExtend 64 = 64 from rfl]
  simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
  rfl

/-- `mid16`: the eight words at `e + 64` added to the columns in one carry
chain and stored there, the carry in `rbp`; `rsi` then at `e + 128`, `rcx`
zero. -/
theorem mid16_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : e + 128 ≤ Z) :
    WP isa (.block AdxTiledSquare.mid16) s fun t =>
      wv t.mem B (e+64) 8 + 2^512 * (t.gpr .rbp).toNat = cols s + wv s.mem B (e+64) 8 ∧
      Outside B (e+64) 64 s.mem t.mem ∧ t.gpr .rsi = off B (e+128) ∧ t.gpr .rcx = 0 ∧
      Keep [.rax,.rbp,.rcx,.rsi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  have nowrap := hs.nowrap
  unfold AdxTiledSquare.mid16
  rw [show ([.alu .add .rsi (.imm 64), .alu32 .xor .rax (.reg .rax)] : List Instr) =
    [.alu .add .rsi (.imm 64)] ++ [.alu32 .xor .rax (.reg .rax)] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addRsi_ok hp) fun a ⟨pa,ma,ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (AdxRotate8.xorRax_ok a) fun b ⟨zb,cb,kb⟩ => ?_
  rw [WP.block_append_iff]
  have src : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] b t →
      readSrc t (.mem (AdxRotate8.at_ .rsi (8 * k))) = some (word s.mem B (e + 64 + 8 * k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h),
      kb.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h)]
    have pa' : a.gpr .rsi = off B (e+64) := pa
    rw [← ma]
    exact readSrc_word (hs.congr ka.2.2) (AdxRotate8.ea_at pa' (8 * k)) (by omega)
  refine WP.mono (AdxRotate8.chain_ok b _ _ cb src (fun _ _ _ h => nomatch h)) fun c ⟨cc, hcc, ec, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (AdxCarry8.close_ok c hcc ((kc.gpr (by decide)).trans zb)) fun d ⟨ed,kd⟩ => ?_
  rw [WP.block_append_iff]
  have kad := ka.trans (kb.keep.trans (kc.keep.trans kd.keep))
  have pd : d.gpr .rsi = off B (e+64) := by
    rw [kd.gpr (by decide), kc.gpr (by decide), kb.gpr (by decide)]; exact pa
  refine WP.mono (AdxRotate8.storeCols_ok (hs.congr kad.2.2) pd (by omega)) fun f ⟨vf,of,kf⟩ => ?_
  rw [show ([.alu .add .rsi (.imm 64), .mov32 .rcx (.imm 0)] : List Instr) =
    [.alu .add .rsi (.imm 64)] ++ [.mov32 .rcx (.imm 0)] from rfl, WP.block_append_iff]
  refine WP.mono (addRsi_ok ((kf.gpr (by decide)).trans pd)) fun g ⟨pg,mg,kg⟩ => ?_
  refine WP.mono (movZero_ok g .rcx) fun t ⟨zt,_,_,kt⟩ => ?_
  have cA := cols_keep ka (by decide)
  have cB := cols_keep kb.keep (by decide)
  have cD := cols_keep kd.keep (by decide)
  rw [AdxRotate8.number_words, cB, cA] at ec
  simp only [Bool.toNat_false, Nat.add_zero] at ec
  have mem_d : d.mem = a.mem := by rw [kd.2.1, kc.2.1, kb.2.1]
  have rbp_t : t.gpr .rbp = d.gpr .rbp := by
    rw [kt.gpr (by decide), kg.gpr (by decide), kf.gpr (by decide)]
  refine ⟨?_, ?_, (kt.gpr (by decide)).trans pg, zt, ?_⟩
  · rw [kt.2.1, mg, vf, rbp_t, ed, cD]
    omega_using [ec]
  · rw [kt.2.1, mg]
    rw [mem_d, ma] at of
    exact of
  · exact ((kad.trans kf).trans (kg.trans kt.keep)).mono (by decide)

private theorem cross16_arith {W0 W1 W2 W3 L1 Y C2 b X3 c A P : Nat}
    (h1 : L1 + P*Y = W1 + A) (h2 : C2 + P*b = Y + W2) (h3 : X3 + P*c = W3 + b) :
    W0 + P*(L1 + P*(C2 + P*X3)) + P*(P*(P*(P*c))) = W0 + P*(W1 + P*(W2 + P*W3)) + P*A := by
  have e1 : P*(L1 + P*Y) = P*(W1 + A) := by rw [h1]
  have e2 : P*P*(C2 + P*b) = P*P*(Y + W2) := by rw [h2]
  have e3 : P*P*P*(X3 + P*c) = P*P*P*(W3 + b) := by rw [h3]
  grind

private theorem split32 (m : Mem) (B : Addr) (R : Nat) : wv m B R 32 =
    wv m B R 8 + 2^512 * (wv m B (R+64) 8 + 2^512 * (wv m B (R+128) 8 + 2^512 * wv m B (R+192) 8)) := by
  rw [show (32 : Nat) = 8+(8+(8+8)) from rfl, wv_add, wv_add, wv_add, show R+8*8 = R+64 by omega,
    show R+64+8*8 = R+128 by omega, show R+128+8*8 = R+192 by omega, show (64 : Nat)*8 = 512 from rfl]

/-- The 16-word square's cross tile: `a[0..8) * a[8..16)` added at word 8 of
the raw product, a carry out of its top word aside. -/
theorem cross16_ok {s : State} {B : Addr} {Z w a : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi) (hZ : slot w 8 ≤ Z)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca : Nat} (pa : (ca, a) ∈ ps)
    (hw : w = 16) (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    WP isa (AdxTiledSquare.cross16 ca) s fun t =>
      (∃ c, wv t.mem B (rawBase w) 32 + 2^512*(2^512*(2^512*(2^512*c))) =
        wv s.mem B (rawBase w) 32 + 2^512 * (wv s.mem B (slot w a) 8 * wv s.mem B (slot w a+64) 8)) ∧
      Hdr t.mem B w mi ∧ Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  subst hw
  have nowrap := hs.nowrap
  have sa := slot_le (w := 16) ha
  have s1 := slot_sep (w := 16) ha1
  have s2 := slot_sep (w := 16) ha2
  have hZ64 : Z ≤ 2^64 := by omega
  -- the raw product at `R`, past the header slots, before the end, apart from `a`
  have st := slot_le (w := 16) (show aTmp < 8 by decide)
  have rawZ : rawBase 16 + 256 ≤ Z := by
    simp only [rawBase, slot, aAcc, aTmp] at st hZ ⊢; omega_using [st, hZ]
  have rawH : 8*sFn 12 + 32 ≤ rawBase 16 := by unfold rawBase slot hdrBytes sFn; omega
  have sep : slot 16 a + 128 ≤ rawBase 16 + 64 ∨ rawBase 16 + 256 ≤ slot 16 a := by
    simp only [rawBase, slot, aAcc, aTmp] at s1 s2 ⊢; omega_using [s1, s2]
  have aZ : slot 16 a + 128 ≤ Z := by omega_using [sa, hZ]
  have hRa : slot 16 aAcc + 16 + 8*(0+8) = rawBase 16 + 64 := by unfold rawBase; omega
  generalize hR : rawBase 16 = R at *
  unfold AdxTiledSquare.cross16
  -- the tile's indices
  refine WP.seq (WP.mono (init16_ok hs hd hZ) fun u ⟨iu,ju,ou,ku⟩ => ?_)
  have fu : Frm B (ranges 16) s.mem u.mem :=
    Frm.of_outside (ou.mono (o' := 8*sFn 12) (n' := 32) (by omega_using []) (by omega_using []))
      (by simp [ranges, hR])
  -- its addresses
  refine WP.seq (WP.mono (AdxRect8.setup_ok (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd)
    (frame_hdr hh fu) hZ (AdxTiledProduct.frame_ops hv fu) pa pa iu ju) fun v ⟨va,vb,vo,mv,kv⟩ => ?_)
  rw [hRa] at vo
  simp only [Nat.mul_zero, Nat.add_zero] at va
  -- the columns
  refine WP.seq (WP.mono (AdxRotate8.loadCols_ok (hs.congr (ku.trans kv).2.2) vo
    (by omega_using [rawZ])) fun x ⟨cx,kx⟩ => ?_)
  have kvx := (ku.trans kv).trans kx.keep
  have xu : x.mem = u.mem := by rw [kx.2.1, mv]
  -- the tile's products
  refine WP.seq (WP.mono (AdxRotate8.productN_disjoint_ok (n := 8) (hs.congr kvx.2.2)
    ((kx.gpr (by decide)).trans va) ((kx.gpr (by decide)).trans vb) ((kx.gpr (by decide)).trans vo)
    (by omega_using [aZ]) (by omega_using [rawZ]) (by omega_using [aZ]) (by omega_using [sep])
    (by omega_using [sep])) fun y ⟨ey,oy,ky⟩ => ?_)
  have kvy := kvx.trans ky
  -- the next eight words, the carry
  refine WP.seq (WP.mono (mid16_ok (hs.congr kvy.2.2) ((ky.gpr (by decide)).trans ((kx.gpr (by decide)).trans vo))
    (by omega_using [rawZ])) fun z ⟨ez,oz,pz,cz,kz⟩ => ?_)
  have kvz := kvy.trans kz
  rw [show R+64+64 = R+128 by omega_using []] at ez oz
  rw [show R+64+128 = R+192 by omega_using []] at pz
  -- the carry through the words above
  refine WP.mono (AdxCarry8.block8_ok (hs.congr kvz.2.2) pz (by omega_using [rawZ]) cz)
    fun t ⟨et,_,ot,kt⟩ => ?_
  -- the memory, block by block
  have R64 : R + 256 ≤ 2^64 := by omega_using [rawZ, hZ64]
  have rawU (d : Nat) (hd : R ≤ d) (hk : d + 64 ≤ R + 256) : wv u.mem B d 8 = wv s.mem B d 8 :=
    ou.wv (Or.inr (by omega_using [hd, rawH])) (by omega_using [hk, R64])
  have b0 : wv t.mem B R 8 = wv s.mem B R 8 := by
    rw [ot.wv (Or.inl (by omega_using [])) (by omega_using [R64]),
      oz.wv (Or.inl (by omega_using [])) (by omega_using [R64]),
      oy.wv (Or.inl (by omega_using [])) (by omega_using [R64]), xu,
      rawU R (by omega_using []) (by omega_using [])]
  have b1 : wv t.mem B (R+64) 8 = wv y.mem B (R+64) 8 := by
    rw [ot.wv (Or.inl (by omega_using [])) (by omega_using [R64]),
      oz.wv (Or.inl (by omega_using [])) (by omega_using [R64])]
  have b2 : wv t.mem B (R+128) 8 = wv z.mem B (R+128) 8 :=
    ot.wv (Or.inl (by omega_using [])) (by omega_using [R64])
  have y2 : wv y.mem B (R+128) 8 = wv s.mem B (R+128) 8 := by
    rw [oy.wv (Or.inr (by omega_using [])) (by omega_using [R64]), xu,
      rawU _ (by omega_using []) (by omega_using [])]
  have z3 : wv z.mem B (R+192) 8 = wv s.mem B (R+192) 8 := by
    rw [oz.wv (Or.inr (by omega_using [])) (by omega_using [R64]),
      oy.wv (Or.inr (by omega_using [])) (by omega_using [R64]), xu,
      rawU _ (by omega_using []) (by omega_using [])]
  have w1 : cols x = wv s.mem B (R+64) 8 := by
    rw [cx, mv, rawU _ (by omega_using []) (by omega_using [])]
  have inA (d : Nat) (hd : slot 16 a ≤ d) (hd' : d + 64 ≤ slot 16 a + 128) :
      wv x.mem B d 8 = wv s.mem B d 8 := by
    rw [xu]
    exact ou.wv (Or.inr (by unfold slot hdrBytes sFn at *; omega_using [hd])) (by omega_using [hd', aZ, hZ64])
  rw [inA _ (Nat.le_refl _) (by omega_using []), inA _ (by omega_using []) (by omega_using []), w1] at ey
  rw [y2] at ez
  rw [z3] at et
  have wide (o n : Nat) {m m' : Mem} (h : Outside B o n m m') (h1 : R ≤ o) (h2 : o + n ≤ R + 16*16) :
      Frm B (ranges 16) m m' :=
    Frm.of_outside (h.mono (o' := R) (n' := 16*16) h1 h2) (by simp [ranges, hR])
  have fx : Frm B (ranges 16) s.mem x.mem := by rw [xu]; exact fu
  have ft : Frm B (ranges 16) s.mem t.mem :=
    ((fx.trans (wide _ _ oy (by omega_using []) (by omega_using []))).trans
      (wide _ _ oz (by omega_using []) (by omega_using []))).trans (wide _ _ ot (by omega_using []) (by omega_using []))
  refine ⟨⟨(t.gpr .rbp).toNat, ?_⟩, frame_hdr hh ft, ft, (kvz.trans kt).mono (by decide)⟩
  rw [split32, split32, b0, b1, b2]
  rw [show (64 : Nat)*8 = 512 from rfl] at ey
  generalize (2 : Nat)^512 = P at ey ez et ⊢
  exact cross16_arith ey ez et

end VG.Proof.Bignum.X86_64.AdxTiledSquare
