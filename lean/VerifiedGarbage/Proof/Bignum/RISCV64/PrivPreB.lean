module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreA
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPower
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: a factor's `R² mod p`

`maskLoop_ok`: the end of `prime`, `w` words of the factor's working space,
and-ed with the mask, to `pre`; `prime_ok`: `prime xj`, as
`vg_rsa_private_crt`'s `power` starts (`Win.powerA_ok`), then those words,
and `pre`'s cursor in the header advanced past them.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (cmask and_mask)

/-- The loop of `prime`'s end: the `w` words at `t4` (`d` in the working
space at `B`), and-ed with the mask of `b` (`t1`), to `t3` (`o` in `pre` at
`P`, apart from the working space), both advanced past them. -/
theorem maskLoop_ok {s : State} {B P : Addr} {Z L d o w : Nat} {b : Bool} (hs : Scr s B Z)
    (hp : Scr s P L) (hsep : ∀ x, ofs P x < L → Z ≤ ofs B x)
    (h4 : s.gpr .t4 = Mont.off B d) (h3 : s.gpr .t3 = Mont.off P o) (h5 : s.gpr .t5 = BitVec.ofNat 64 w)
    (h1 : s.gpr .t1 = cmask b) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) (hd8 : d % 8 = 0)
    (ho : o + 8 * w ≤ L) (ho8 : o % 8 = 0) :
    WP isa (countLoop .t5 [.load .d .s0 .t4 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8]) s fun t =>
      ((∀ i < w, Mont.word t.mem P (o + 8 * i) = if b then Mont.word s.mem B (d + 8 * i) else 0) ∧
        t.gpr .t3 = Mont.off P (o + 8 * w) ∧ Mont.Outside P o (8 * w) s.mem t.mem) ∧
        Keep [.s0, .t3, .t4, .t5] s t := by
  have hnB := hs.nowrap
  have hnP := hp.nowrap
  -- The working space's words are apart from `pre`'s.
  have keepB : ∀ {m m' : Mem} {o' n : Nat}, Mont.Outside P o' n m m' → o' + n ≤ L → ∀ e, e + 8 ≤ Z →
      Mont.word m' B e = Mont.word m B e := fun {m m' o' n} h hn e he => Mem.readW_congr fun i hi => h _ (by
    by_contra hc
    have hc' : ofs P (Mont.off B e + BitVec.ofNat 64 i) < L := by simp only [Mont.ofs, VG.Proof.Bignum.ofs] at hc ⊢; omega_arith
    have := hsep _ hc'
    rw [ofs_off _ (by omega_arith)] at this
    omega_arith)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t4 = Mont.off B (d + 8 * i) ∧ t.gpr .t3 = Mont.off P (o + 8 * i) ∧ t.gpr .t1 = cmask b ∧
      (∀ j < i, Mont.word t.mem P (o + 8 * j) = if b then Mont.word s.mem B (d + 8 * j) else 0) ∧
      Mont.Outside P o (8 * i) s.mem t.mem ∧ Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t4 0, .logic .and .s0 .s0 .t1,
      .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j4, j3, j1, jw, jout, jk⟩ _ => ?_)
    ⟨by rw [h4]; rfl, by rw [h3]; rfl, h1, fun _ h => absurd h (Nat.not_lt_zero _), Mont.Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by decide)⟩ h5)
    fun t ⟨_, t3, _, tw, tout, tk⟩ => ⟨⟨tw, t3, tout⟩, tk⟩
  have hwd : Mont.word t.mem B (d + 8 * i) = Mont.word s.mem B (d + 8 * i) :=
    keepB jout (by omega_arith) _ (by omega_arith)
  refine WP.mono (WP.keep [.s0, .t3, .t4, .t5] (Q := fun t' =>
    t'.mem = t.mem.writeW (Mont.off P (o + 8 * i)) (Mont.word t.mem B (d + 8 * i) &&& cmask b) ∧
      t'.gpr .t4 = Mont.off B (d + 8 * (i + 1)) ∧ t'.gpr .t3 = Mont.off P (o + 8 * (i + 1)) ∧
      t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
    fun t' ⟨⟨a, b4, b3, c⟩, k⟩ => ⟨⟨b4, b3, (k.gpr (by decide)).trans j1, ?_, ?_, Keep.trans' jk k⟩, c⟩
  · brun [add_ofNat_zero, j4, j3, j1, (hs.congr jk.2.2).ld (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hs.congr jk.2.2).al8 (show d + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      (hp.congr jk.2.2).st (show o + 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.2.2).al8 (show o + 8 * i + 8 ≤ L by omega_arith) (by omega_arith)]
    rw [show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith, show o + 8 * i + 8 = o + 8 * (i + 1) by omega_arith]
    exact ⟨rfl, rfl⟩
  · intro j hj
    have hw := Mont.writeW_outside t.mem P (d := o + 8 * i) (Mont.word t.mem B (d + 8 * i) &&& cmask b)
      (by omega_arith)
    rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.word (by omega_arith) (by omega_arith)]; exact jw j hj
    · rw [Mont.word_writeW_self, hwd, and_mask]
  · have hw := Mont.writeW_outside t.mem P (d := o + 8 * i) (Mont.word t.mem B (d + 8 * i) &&& cmask b)
      (by omega_arith)
    rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))

/-- The words of `prime`'s result: `R² mod p`'s, or zeros. -/
abbrev r2Word (b : Bool) (w Pv i : Nat) : BitVec 64 :=
  if b then BitVec.ofNat 64 (2 ^ (128 * w) % Pv / 2 ^ (64 * i)) else 0

/-- The registers `prime` writes. -/
def primeAllRegs : List Reg := Win.powerRegs ++ [.t4, .t3, .t1, .t5] ++ [.s0, .t3, .t4, .t5]

/-- What `prime xj` needs: for the factor `Pv` in `X`'s array `xj` (`X` at
`BX`, in `s6`, its arrays' size in `s11`), its working space at `BX + oA`
(set up), the mask of `b` in the header's `oMask` and `pre`'s cursor `P + o`
in its `oDP`. -/
structure PArgs (s : State) (BX P : Addr) (Z L oA wA wX xj Pv o : Nat) (b : Bool) : Prop where
  hs : Scr s BX Z
  hp : Scr s P L
  hA : oA + slot wA 24 ≤ Z
  hXA : slot wX 8 ≤ oA
  hoA8 : oA % 8 = 0
  hw2 : 2 ≤ wA
  hw' : wA < 2 ^ 31
  hwx : wA ≤ wX
  hxj : xj < 8
  h7 : s.gpr .a7 = Mont.off (Mont.off BX oA) (slot wA 0)
  h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (wA + 2))
  ht0 : s.gpr .t0 = BitVec.ofNat 64 wA
  h6 : s.gpr .s6 = BX
  h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2))
  hcur : Mont.word s.mem BX oDP = Mont.off P o
  hmask : Mont.word s.mem BX oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)
  hP : wordsVal s.mem BX (slot wX xj) wA = Pv
  hP2 : 2 ≤ Pv
  hPodd : Pv % 2 = 1

/-- The header block of `prime`: `t4` := the base of array 1, the cursor
and the mask from the header, and `w` into `t5`. -/
abbrev primeHB : List Instr := VG.Impl.Bignum.RISCV64.PublicChecked.base .t4 1 ++ [.load .d .t3 .s6 oDP, .load .d .t1 .s6 oMask, .addi .t5 .t0 0]

/-- What holds after `prime`'s header block (`v`), with `u` after `powerA`. -/
structure PHead (s : State) (BX P : Addr) (oA wA o Pv : Nat) (b : Bool) (u v : State) : Prop where
  r8 : Win.A u.mem (Mont.off BX oA) wA 1 = 2 ^ (128 * wA) % Pv
  F8 : Win.PFr (Mont.off BX oA) wA s.mem u.mem
  mem : v.mem = u.mem
  t3 : v.gpr .t3 = Mont.off P o
  t1 : v.gpr .t1 = cmask b
  t5 : v.gpr .t5 = BitVec.ofNat 64 wA
  t4 : v.gpr .t4 = Mont.off (Mont.off BX oA) (slot wA 1)
  keep : Keep (Win.powerRegs ++ [.t4, .t3, .t1, .t5]) s v

/-- `prime xj` to its header block, as `prime_ok`, then `c`. -/
theorem primeHead_ok {s : State} {BX P : Addr} {Z L oA wA wX xj Pv o : Nat} {b : Bool} {c : Prog isa}
    {Q : State → Prop} (H : PArgs s BX P Z L oA wA wX xj Pv o b)
    (hc : ∀ u v, PHead s BX P oA wA o Pv b u v → WP isa c v Q) :
    WP isa (Win.powerP xj (.seq (.block primeHB) c)) s Q := by
  obtain ⟨hs, hp, hA, hXA, hoA8, hw2, hw', hwx, hxj, h7, h5, ht0, h6, h11, hcur, hmask, hP, hP2, hPodd⟩ := H
  have hnB := hs.nowrap
  have hnP := hp.nowrap
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA24 := e wA 24; have eX8 := e wX 8; have eXj := e wX xj
  have hS : Scr s (Mont.off BX oA) (slot wA 24) := Crt.Scr.sub hs hA hoA8 (by omega_arith)
  have hX : Scr s BX (slot wX 8) := Crt.Scr.le hs (by omega_arith)
  have hsepXA : ∀ x, ofs BX x < slot wX 8 → slot wA 24 ≤ ofs (Mont.off BX oA) x :=
    Crt.sepXB hXA (by omega_arith) (by omega_arith)
  refine Win.powerA_ok hS hw2 hw' (Nat.le_refl _) h7 h5 ht0 hX hsepXA h6 h11
    (by have := VG.Proof.Bignum.slot_le (w := wX) (show xj < 8 from hxj); omega_arith) hP hP2 hPodd
    fun u c8 r8 F8 k8 => ?_
  have hdr : ∀ d, d + 8 ≤ slot wX 8 → Mont.word u.mem BX d = Mont.word s.mem BX d := fun d hd =>
    VG.Proof.Bignum.RISCV64.Outside.word_sep F8 hsepXA (by rw [Win.slot24']) hd (by omega_arith)
  have k6 : u.gpr .s6 = BX := (k8.gpr (by decide)).trans h6
  -- `t4`, `t3` (the cursor), `t1` (the mask) and `t5`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) c8.a7 c8.s5 1) fun u1 ⟨⟨u14, um1⟩, uk1⟩ => ?_
  have hcur' : u1.mem.readW (Mont.off BX 64) 64 = Mont.off P o := by
    rw [um1]; exact (hdr oDP (by unfold oDP; omega_arith)).trans hcur
  have hmask' : u1.mem.readW (Mont.off BX 88) 64 = cmask b := by
    rw [um1]; exact ((hdr oMask (by unfold oMask; omega_arith)).trans hmask).trans (Crt.cmask_sub b).symm
  have u16 : u1.gpr .s6 = Mont.off BX 0 := by rw [uk1.gpr (by decide), k6]; exact (BitVec.add_zero _).symm
  have hs1 := hs.congr (k8.trans uk1).2.2
  refine WP.mono (WP.keep [.t3, .t1, .t5] (Q := fun v => v.gpr .t3 = Mont.off P o ∧ v.gpr .t1 = cmask b ∧
      v.gpr .t5 = BitVec.ofNat 64 wA ∧ v.mem = u1.mem) (by
        brun [u16, (uk1.gpr (by decide)).trans c8.t0, add_ofNat_zero, off_add, oDP, oMask,
          hs1.ld (show 64 + 8 ≤ Z by omega_arith), hs1.al8 (show 64 + 8 ≤ Z by omega_arith) (by decide),
          hs1.ld (show 88 + 8 ≤ Z by omega_arith), hs1.al8 (show 88 + 8 ≤ Z by omega_arith) (by decide),
          hcur', hmask'])
      (by rfl) (by rfl)) fun v ⟨⟨v3, v1, v5, vm⟩, vk⟩ => ?_
  exact hc u v ⟨r8, F8, vm.trans um1, v3, v1, v5, (vk.gpr (by decide)).trans u14,
    ((k8.trans uk1).trans vk).mono (by decide)⟩

/-- `prime xj`: for the factor `Pv` in `X`'s array `xj` (`X` at `BX`, in
`s6`, its arrays' size in `s11`), its working space at `BX + oA` (set up),
the mask of `b` in the header's `oMask` and `pre`'s cursor `P + o` in its
`oDP`: `R² mod Pv`'s `w_A` words, or zeros, to `pre` at `P + o`, and the
cursor advanced past them; only those words, the working space and the
cursor changed. -/
theorem prime_ok {s : State} {BX P : Addr} {Z L oA wA wX xj Pv o : Nat} {b : Bool}
    (H : PArgs s BX P Z L oA wA wX xj Pv o b) (hsep : ∀ x, ofs P x < L → Z ≤ ofs BX x)
    (ho : o + 8 * wA ≤ L) (ho8 : o % 8 = 0) :
    WP isa (PrivPre.prime xj) s fun t =>
      ((∀ i < wA, Mont.word t.mem P (o + 8 * i) = r2Word b wA Pv i) ∧
        Mont.word t.mem BX oDP = Mont.off P (o + 8 * wA) ∧
        Frame [⟨Mont.off P o, 8 * wA⟩, ⟨Mont.off BX oA, slot wA 24⟩, ⟨Mont.off BX oDP, 8⟩] s.mem t.mem) ∧
      Keep primeAllRegs s t := by
  have hs := H.hs; have hp := H.hp; have hA := H.hA; have hXA := H.hXA; have hoA8 := H.hoA8
  have hw2 := H.hw2; have hw' := H.hw'; have hwx := H.hwx; have hxj := H.hxj; have h6 := H.h6
  have hnB := hs.nowrap
  have hnP := hp.nowrap
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA24 := e wA 24; have eX8 := e wX 8; have eXj := e wX xj
  have hS : Scr s (Mont.off BX oA) (slot wA 24) := Crt.Scr.sub hs hA hoA8 (by omega_arith)
  have hsepP : ∀ x, ofs P x < L → slot wA 24 ≤ ofs (Mont.off BX oA) x := fun x hx => by
    have h1 := hsep x hx
    simp only [VG.Proof.Bignum.ofs] at h1 ⊢
    rcases Crt.ofs_reb BX x (b := oA) (by omega_arith) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega_arith
  show WP isa (Win.powerP xj (.seq (.block primeHB) (.seq (countLoop .t5 [.load .d .s0 .t4 0,
    .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8])
    (.block [.store .d .t3 .s6 oDP])))) s _
  refine primeHead_ok H fun u v H => ?_
  have r8 := H.r8; have F8 := H.F8
  have v3 := H.t3; have v1 := H.t1; have v5 := H.t5; have v4 := H.t4
  have kv := H.keep
  -- The words.
  refine WP.seq (WP.mono (maskLoop_ok (b := b) (d := slot wA 1) (o := o) (w := wA) (hS.congr kv.2.2)
    (hp.congr kv.2.2) hsepP v4 v3 v5 v1 (by omega_arith) hw' (by omega_arith) (slot_al wA 1)
    ho ho8) fun x ⟨⟨xw, x3, xo⟩, xk⟩ => ?_)
  -- The cursor.
  have kx := kv.trans xk
  have hsx := hs.congr kx.2.2
  refine WP.mono (WP.keep [] (Q := fun y => y.mem = x.mem.writeW (Mont.off BX oDP) (Mont.off P (o + 8 * wA)))
    (by brun [show x.gpr .s6 = Mont.off BX 0 by rw [kx.gpr (by decide), h6]; exact (BitVec.add_zero _).symm, x3,
      off_add, oDP, hsx.st (show 64 + 8 ≤ Z by omega_arith), hsx.al8 (show 64 + 8 ≤ Z by omega_arith) (by decide)])
      (by rfl) (by rfl))
    fun y ⟨ym, yk⟩ => ⟨⟨fun i hi => ?_, ?_, ?_⟩, (kx.trans yk).mono (by decide)⟩
  · -- `pre`'s word, apart from the header's cursor.
    have hw := Mont.writeW_outside x.mem BX (d := oDP) (Mont.off P (o + 8 * wA)) (by unfold oDP; omega_arith)
    have hy : Mont.word y.mem P (o + 8 * i) = Mont.word x.mem P (o + 8 * i) := by
      rw [ym]
      exact Mem.readW_congr fun j hj => hw _ (by
        have h1 := hsep (Mont.off P (o + 8 * i) + BitVec.ofNat 64 j)
          (by
            have e1 := Mont.ofs_off P (d := o + 8 * i) (i := j) (by omega_arith)
            simp only [Mont.ofs] at e1
            simp only [VG.Proof.Bignum.ofs]
            omega_arith)
        simp only [VG.Proof.Bignum.ofs] at h1
        simp only [Mont.ofs]
        unfold oDP; omega_arith)
    rw [hy, xw i hi, H.mem]
    unfold r2Word
    split
    · apply BitVec.eq_of_toNat_eq
      have h := VG.Proof.Bignum.word_of_wv u.mem (Mont.off BX oA) (slot wA 1) wA hi
      rw [← Pre.wordsVal_eq_wv, show wordsVal u.mem (Mont.off BX oA) (slot wA 1) wA = 2 ^ (128 * wA) % Pv
        from r8] at h
      rw [BitVec.toNat_ofNat]
      exact h
    · rfl
  · rw [ym]; exact Mont.word_writeW_self _ _ _ _
  · -- Only `pre`'s words, the working space and the cursor changed.
    rw [ym]
    refine Frame.trans (fun z hz => ?_) ((Frame.refl _ x.mem).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith))
    have h1 := hz _ (List.mem_cons_self ..)
    have h2 := hz _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [Region.Contains] at h1 h2
    rw [show Mont.off P o = P + BitVec.ofNat 64 o from rfl] at h1
    have I1 := Offset.lt_iff z P (d := o) (n := 8 * wA) (by omega_arith)
    rw [xo z (by
      simp only [Mont.ofs]
      by_cases hc : o ≤ (z - P).toNat ∧ (z - P).toNat < o + 8 * wA
      · exact absurd (I1.mpr hc) (by omega_arith)
      · omega_arith), H.mem]
    exact F8 z (Or.inr (by change _ ≤ (z - Mont.off BX oA).toNat; omega_arith))

end VG.Proof.Bignum.RISCV64.PrivPre
