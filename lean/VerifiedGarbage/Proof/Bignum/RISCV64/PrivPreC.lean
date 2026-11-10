module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreB
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the factors

`partB_ok`: after the checks (`A`), each factor's `R² mod p` (or zeros) to
`pre` after `n`'s values (`prime_ok`), `p`'s then `q`'s (`B`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf wordsOf_ge two_le_wordsOf wordsOf_le_of wordsVal_trunc savW)

/-- An address in the region at `B + o` of `n` bytes is at those offsets. -/
theorem in_of_contains {B y : Addr} {o n : Nat} (h : (⟨Mont.off B o, n⟩ : Region).Contains y 1)
    (hn : o + n ≤ 2 ^ 64) : o ≤ (y - B).toNat ∧ (y - B).toNat < o + n := by
  have I := Offset.lt_iff y B hn
  change (y - Mont.off B o).toNat + 1 ≤ n at h
  exact I.mp (by change (y - Mont.off B o).toNat < n; omega_arith)

theorem ofs_off' (B : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    (Mont.off B d + BitVec.ofNat 64 i - B).toNat = d + i := Mont.ofs_off B h

/-- The regions `prime` changes: `pre`'s segment, the working space, and the
header's cursor. -/
abbrev primeR (P S : Addr) (o n oA L : Nat) : List Region :=
  [⟨Mont.off P o, n⟩, ⟨Mont.off S oA, L⟩, ⟨Mont.off S oDP, 8⟩]

/-- A word of the working space before `oA`, but the header's cursor, after
`prime`. -/
theorem frame_word {m m' : Mem} {P S : Addr} {o n oA L Z PL d : Nat}
    (F : Frame (primeR P S o n oA L) m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hon : o + n ≤ PL) (hd : d + 8 ≤ oA) (hdp : d + 8 ≤ oDP ∨ oDP + 8 ≤ d) (hZ : oA + L ≤ Z)
    (hnw : S.toNat + Z ≤ 2 ^ 64) (hPn : P.toNat + PL ≤ 2 ^ 64) :
    Mont.word m' S d = Mont.word m S d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' S (d := d) (i := i) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    have := hsep (Mont.off S d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
    change _ ≤ (_ - S).toNat at this
    omega_arith
  · have := in_of_contains hc (by omega_arith)
    omega_arith
  · have := in_of_contains hc (by unfold oDP; omega_arith)
    omega_arith

/-- A word of `pre` apart from its changed segment, after `prime`. -/
theorem frame_word_pre {m m' : Mem} {P S : Addr} {o n oA L Z PL d : Nat}
    (F : Frame (primeR P S o n oA L) m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ PL) (hZ : oA + L ≤ Z) (hZ' : oDP + 8 ≤ Z)
    (hPn : P.toNat + PL ≤ 2 ^ 64) (hon : o + n ≤ PL) :
    Mont.word m' P d = Mont.word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' P (d := d) (i := i) (by omega_arith)
  have hs := hsep (Mont.off P d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
  change _ ≤ (_ - S).toNat at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    omega_arith
  · have := in_of_contains hc (by omega_arith)
    omega_arith
  · have := in_of_contains hc (by omega_arith)
    omega_arith

/-- A number of the working space before `oA` and the header's cursor,
after `prime`. -/
theorem frame_wv {m m' : Mem} {P S : Addr} {o n oA L Z PL d k : Nat}
    (F : Frame (primeR P S o n oA L) m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hon : o + n ≤ PL) (hd : d + 8 * k ≤ oA) (hdp : oDP + 8 ≤ d) (hZ : oA + L ≤ Z)
    (hnw : S.toNat + Z ≤ 2 ^ 64) (hPn : P.toNat + PL ≤ 2 ^ 64) :
    wordsVal m' S d k = wordsVal m S d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [wordsVal]
    rw [frame_word F hsep hon (by omega_arith) (Or.inr hdp) hZ hnw hPn, ih (by omega_arith) (by omega_arith)]

/-- The factors' words. -/
abbrev cwP (s : State) : Nat := wordsOf (cpL s)
abbrev cwQ (s : State) : Nat := wordsOf (cqL s)

theorem r2Word_mask (b : Bool) (w P i : Nat) : r2Word b w (if b then P else 3) i = r2Word b w P i := by
  cases b <;> rfl

/-- The facts of the factors' values. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    (2 ≤ (if cb s₀ then cP s₀ else 3) ∧ (if cb s₀ then cP s₀ else 3) % 2 = 1 ∧
      (if cb s₀ then cP s₀ else 3) < 2 ^ (64 * cwP s₀)) ∧
    (2 ≤ (if cb s₀ then cQ s₀ else 3) ∧ (if cb s₀ then cQ s₀ else 3) % 2 = 1 ∧
      (if cb s₀ then cQ s₀ else 3) < 2 ^ (64 * cwQ s₀)) := by
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by have := wordsOf_ge (l := cpL s₀); omega_arith
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by have := wordsOf_ge (l := cqL s₀); omega_arith
  have wP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have wQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have h3p : 3 < 2 ^ (64 * cwP s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwP s₀ by omega_arith))
  have h3q : 3 < 2 ^ (64 * cwQ s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwQ s₀ by omega_arith))
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨by decide, by decide, h3p⟩, ⟨by decide, by decide, h3q⟩⟩
  · simp only [↓reduceIte]
    have hb' : Crt.crtMask (cN s₀) (ck s₀) (Spec.Rsa.os2ip []) (cP s₀) (cQ s₀) (Spec.Rsa.os2ip []) = true := by
      rw [show Spec.Rsa.os2ip [] = 0 from rfl, crtMask_zero]; exact hb
    obtain ⟨_, _, _, _, hp1, hpo, hq1, hqo⟩ := Crt.mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb'
    exact ⟨⟨hp1, hpo, Nat.lt_of_lt_of_le (Crt.os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (Crt.pow256_le hpw)⟩,
      ⟨hq1, hqo, Nat.lt_of_lt_of_le (Crt.os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (Crt.pow256_le hqw)⟩⟩

/-- The factors' first block: the header's cursor `:= pre + 16 w`, and `p`'s
working space. -/
theorem partB1_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) :
    WP isa (.block (([.load .d .t3 .s6 oOut, .load .d .t4 .s6 oNLen, .addi .t4 .t4 7, .shift .srl .d .t4 .t4 3,
      .shift .sll .d .t4 .t4 4, .add .t3 .t3 .t4, .store .d .t3 .s6 oDP] : List Instr) ++ setupP oBP oPLen)) t
      fun v =>
        (v.gpr .a7 = Mont.off (Mont.off (cS s₀) (slot (cwX s₀) 8)) (slot (cwP s₀) 0) ∧
          v.gpr .s5 = BitVec.ofNat 64 (8 * (cwP s₀ + 2)) ∧ v.gpr .t0 = BitVec.ofNat 64 (cwP s₀) ∧
          v.mem = t.mem.writeW (Mont.off (cS s₀) oDP) (Mont.off (s₀.gpr .a0) (16 * cw s₀))) ∧
        Keep (([.t3, .t4] : List Reg) ++ ([.t2, .t3, .t4, .a7, .ra, .s5, .t0] : List Reg)) t v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have p1 := hP.p1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have eX8 := e (cwX s₀) 8
  have hcw : cwX s₀ = 2 * (((s₀.gpr .a3).toNat + 7) / 8) := rfl
  have hwP := wordsOf_ge (l := cpL s₀)
  have hwQ := wordsOf_ge (l := cqL s₀)
  have hZ : 112 ≤ cZ s₀ := by omega_arith
  have hs := hA.scr
  have z : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
  have hO : t.mem.readW (cS s₀) 64 = s₀.gpr .a0 := by rw [← z]; exact hA.hOut
  have l0 : InRegions (t.rd ++ t.wr) (cS s₀) 8 := by rw [← z]; exact hs.ld (by omega_arith)
  have hK : t.mem.readW (Mont.off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) :=
    hA.hNL.trans (Pre.ofNat_toNat64 _).symm
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3, .t4] (Q := fun u =>
      u.mem = t.mem.writeW (Mont.off (cS s₀) oDP) (Mont.off (s₀.gpr .a0) (16 * cw s₀)))
    (by
      brun [hA.s6, add_ofNat_zero, oOut, oNLen, oDP, l0, hs.al, hs.ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
        hs.al8 (show 16 + 8 ≤ cZ s₀ by omega_arith) (by decide), hs.st (show 64 + 8 ≤ cZ s₀ by omega_arith),
        hs.al8 (show 64 + 8 ≤ cZ s₀ by omega_arith) (by decide), hO, hK, BitVec.ofNat_add_ofNat,
        Crt.ofNat_shr3 (ck s₀ + 7) (by omega_arith), Crt.ofNat_shl _ _ (show 4 < 64 by decide), Nat.reducePow])
    (by rfl) (by rfl)) fun u ⟨um, uk⟩ => ?_
  have hu : ∀ d, d + 8 ≤ oDP ∨ oDP + 8 ≤ d → d + 8 ≤ cZ s₀ → Mont.word u.mem (cS s₀) d = Mont.word t.mem (cS s₀) d :=
    fun d hd hd' => by
      rw [um]
      exact (Mont.writeW_outside t.mem (cS s₀) (d := oDP) _ (by unfold oDP; omega_arith)).word hd (by omega_arith)
  refine WP.mono (Crt.setupP_ok (hs.congr uk.2.2) (by rw [uk.gpr (by decide), hA.s6]; exact z.symm)
    (by unfold oBP; omega_arith) (by decide) (by decide) (by unfold oPLen; omega_arith) (by decide) (by decide)
    (by rw [hu _ (by unfold oDP oBP; omega_arith) (by unfold oBP; omega_arith)]; exact hA.hBP)
    (by rw [hu _ (by unfold oDP oPLen; omega_arith) (by unfold oPLen; omega_arith), hA.hPL];
        exact (Pre.ofNat_toNat64 _).symm) p1 (by omega_arith))
    fun v ⟨⟨v7, _, v5, v0, _, vm⟩, vk⟩ => ⟨⟨v7, v5, v0, vm.trans um⟩, uk.trans vk⟩

/-- The first block of the factors. -/
abbrev curBlock : List Instr :=
  [.load .d .t3 .s6 oOut, .load .d .t4 .s6 oNLen, .addi .t4 .t4 7, .shift .srl .d .t4 .t4 3,
    .shift .sll .d .t4 .t4 4, .add .t3 .t3 .t4, .store .d .t3 .s6 oDP]

/-- `q`'s working space's offset in `X`'s, as the header's `oBQ` gives it. -/
abbrev oAQ (s₀ : State) : Nat := slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2))

/-- The registers written up to the factors. -/
def bRegs : List Reg :=
  aRegs ++ (([.t3, .t4] ++ [.t2, .t3, .t4, .a7, .ra, .s5, .t0]) ++ primeAllRegs ++
    [.t2, .t3, .t4, .a7, .ra, .s5, .t0]) ++ primeAllRegs

/-- What holds after the factors, from the entry state `s₀`. -/
structure B (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hMask : Mont.word s.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  s6 : s.gpr .s6 = cS s₀
  wP : ∀ i < cwP s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  keep : Keep bRegs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

/-- After the factors' first block: `p`'s arguments. -/
structure BV (s₀ t v : State) : Prop where
  pa : PArgs v (cS s₀) (s₀.gpr .a0) (cZ s₀) ((s₀.gpr .a1).toNat * 8) (slot (cwX s₀) 8) (cwP s₀) (cwX s₀) 4
    (if cb s₀ then cP s₀ else 3) (16 * cw s₀) (cb s₀)
  keep : Keep ([.t3, .t4] ++ [.t2, .t3, .t4, .a7, .ra, .s5, .t0]) t v
  mem : v.mem = t.mem.writeW (Mont.off (cS s₀) oDP) (Mont.off (s₀.gpr .a0) (16 * cw s₀))

/-- After the checks, the factors' first block. -/
theorem partBv_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ v, BV s₀ t v → WP isa c v Q) :
    WP isa (.seq (.block (curBlock ++ setupP oBP oPLen)) c) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have dcpL : cpL s₀ = (s₀.gpr .a5).toNat := rfl
  have dcqL : cqL s₀ = (s₀.gpr .a7).toNat := rfl
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dAQ : oAQ s₀ = slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have eX8 := e (cwX s₀) 8; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  have eP24' := e (wordsOf (cpL s₀)) 24; have eQ24' := e (wordsOf (cqL s₀)) 24
  have eX8' := e (2 * ((ck s₀ + 7) / 8)) 8
  have wP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have wQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have wPX : cwP s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  have wQX : cwQ s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  have hPS := hP.sepPre
  refine WP.seq (WP.mono (partB1_ok hP hA) fun v ⟨⟨v7, v5, v0, vm⟩, vk⟩ => hc v ⟨?_, vk, vm⟩)
  have kv := hA.keep.trans vk
  have hv : ∀ d, d + 8 ≤ oDP ∨ oDP + 8 ≤ d → d + 8 ≤ cZ s₀ → Mont.word v.mem (cS s₀) d = Mont.word t.mem (cS s₀) d :=
    fun d hd hd' => by
      rw [vm]
      exact (Mont.writeW_outside t.mem (cS s₀) (d := oDP) _ (by unfold oDP; omega_arith)).word hd (by omega_arith)
  have hvO : Mont.Outside (cS s₀) oDP 8 t.mem v.mem := by
    rw [vm]; exact Mont.writeW_outside t.mem (cS s₀) (d := oDP) _ (by unfold oDP; omega_arith)
  exact ⟨hA.scr.congr vk.2.2, hP.pre.congr kv.2.2, by omega_arith, Nat.le_refl _, by omega_arith, wP2,
    by omega_arith, by omega_arith, by decide, v7, v5, v0, by rw [vk.gpr (by decide)]; exact hA.s6,
    by rw [vk.gpr (by decide)]; exact hA.s11, by rw [vm]; exact Mont.word_writeW_self _ _ _ _,
    by rw [hv _ (by unfold oDP oMask; omega_arith) (by unfold oMask; omega_arith)]; exact hA.hMask,
    by rw [hvO.wordsVal (by unfold oDP; omega_arith) (by omega_arith)]
       exact wordsVal_trunc hA.x4 mPb (by omega_arith), mP2, mPo⟩

/-- After `p`'s values and `q`'s working space: `q`'s arguments. -/
structure BY (s₀ t y : State) : Prop where
  pa : PArgs y (cS s₀) (s₀.gpr .a0) (cZ s₀) ((s₀.gpr .a1).toNat * 8) (oAQ s₀) (cwQ s₀) (cwX s₀) 5
    (if cb s₀ then cQ s₀ else 3) (16 * cw s₀ + 8 * cwP s₀) (cb s₀)
  keep : Keep (([.t3, .t4] ++ [.t2, .t3, .t4, .a7, .ra, .s5, .t0]) ++ primeAllRegs ++
    [.t2, .t3, .t4, .a7, .ra, .s5, .t0]) t y
  xw : ∀ i < cwP s₀, Mont.word y.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * i) =
    r2Word (cb s₀) (cwP s₀) (if cb s₀ then cP s₀ else 3) i
  hdr : ∀ d, d + 8 ≤ slot (cwX s₀) 8 → d + 8 ≤ oDP ∨ oDP + 8 ≤ d →
    Mont.word y.mem (cS s₀) d = Mont.word t.mem (cS s₀) d
  frame : Frame [preR s₀, scrR s₀] t.mem y.mem

/-- After the checks, `p`'s values and `q`'s working space. -/
theorem partBy_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ y, BY s₀ t y → WP isa c y Q) :
    WP isa (.seq (.block (curBlock ++ setupP oBP oPLen)) (.seq (PrivPre.prime 4)
      (.seq (.block (setupP oBQ oQLen)) c))) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have dcpL : cpL s₀ = (s₀.gpr .a5).toNat := rfl
  have dcqL : cqL s₀ = (s₀.gpr .a7).toNat := rfl
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dAQ : oAQ s₀ = slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have eX8 := e (cwX s₀) 8; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  have eP24' := e (wordsOf (cpL s₀)) 24; have eQ24' := e (wordsOf (cqL s₀)) 24
  have eX8' := e (2 * ((ck s₀ + 7) / 8)) 8
  have wP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have wQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have wPX : cwP s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  have wQX : cwQ s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  have hPS := hP.sepPre
  refine partBv_ok hP hA fun v V => ?_
  have vk := V.keep
  have kv := hA.keep.trans vk
  have hv : ∀ d, d + 8 ≤ oDP ∨ oDP + 8 ≤ d → d + 8 ≤ cZ s₀ → Mont.word v.mem (cS s₀) d = Mont.word t.mem (cS s₀) d :=
    fun d hd hd' => by
      rw [V.mem]
      exact (Mont.writeW_outside t.mem (cS s₀) (d := oDP) _ (by unfold oDP; omega_arith)).word hd (by omega_arith)
  have hvO : Mont.Outside (cS s₀) oDP 8 t.mem v.mem := by
    rw [V.mem]; exact Mont.writeW_outside t.mem (cS s₀) (d := oDP) _ (by unfold oDP; omega_arith)
  -- `p`'s values.
  refine WP.seq (WP.mono (prime_ok V.pa hPS (by omega_arith) (by omega_arith)) fun x ⟨⟨xw, xcur, xF⟩, xk⟩ => ?_)
  have kx := kv.trans xk
  have tx := vk.trans xk
  have hx : ∀ d, d + 8 ≤ slot (cwX s₀) 8 → d + 8 ≤ oDP ∨ oDP + 8 ≤ d →
      Mont.word x.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd hd' => by
    rw [frame_word xF hPS (by omega_arith) hd hd' (by omega_arith) hn hnP, hv d hd' (by omega_arith)]
  -- `q`'s working space.
  refine WP.seq (WP.mono (Crt.setupP_ok (l := cqL s₀) (Bp := Mont.off (cS s₀) (oAQ s₀)) (hA.scr.congr tx.2.2)
    (by rw [tx.gpr (by decide), hA.s6]; exact (BitVec.add_zero _).symm)
    (by unfold oBQ; omega_arith) (by decide) (by decide) (by unfold oQLen; omega_arith) (by decide) (by decide)
    (by rw [hx _ (by unfold oBQ; omega_arith) (by unfold oDP oBQ; omega_arith)]; exact hA.hBQ)
    (by rw [hx _ (by unfold oQLen; omega_arith) (by unfold oDP oQLen; omega_arith), hA.hQL];
        exact (Pre.ofNat_toNat64 _).symm) q1 (by omega_arith))
    fun y ⟨⟨y7, _, y5, y0, _, ym⟩, yk⟩ => ?_)
  have ky := kx.trans yk
  have ty := tx.trans yk
  have hscr_sub : ∀ {o n : Nat}, o + n ≤ cZ s₀ → Region.Sub ⟨Mont.off (cS s₀) o, n⟩ (scrR s₀) :=
    fun h => Offset.sub_base _ (by omega_arith)
  have F0 : Frame [preR s₀, scrR s₀] t.mem v.mem := by
    rw [V.mem]
    exact ((Frame.refl [⟨Mont.off (cS s₀) oDP, 8⟩] t.mem).writeW (List.mem_singleton_self _) _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)).sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub (by unfold oDP; omega_arith)⟩
  have F1 : Frame [preR s₀, scrR s₀] v.mem x.mem := xF.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨preR s₀, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub (by omega_arith)⟩
    · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub (by unfold oDP; omega_arith)⟩
  refine hc y ⟨⟨hA.scr.congr ty.2.2, hP.pre.congr ky.2.2, by omega_arith, by omega_arith, by omega_arith, wQ2,
    by omega_arith, by omega_arith, by decide, y7, y5, y0, by rw [ty.gpr (by decide)]; exact hA.s6,
    by rw [ty.gpr (by decide)]; exact hA.s11, by rw [ym]; exact xcur,
    by rw [ym, hx _ (by unfold oMask; omega_arith) (by unfold oDP oMask; omega_arith)]; exact hA.hMask,
    by rw [ym, frame_wv xF hPS (by omega_arith) (by omega_arith) (by unfold oDP; omega_arith) (by omega_arith) hn hnP,
          hvO.wordsVal (by unfold oDP; omega_arith) (by omega_arith)]
       exact wordsVal_trunc hA.x5 mQb (by omega_arith), mQ2, mQo⟩, ty, fun i hi => by rw [ym]; exact xw i hi,
    fun d hd hd' => by rw [ym]; exact hx d hd hd', by rw [ym]; exact (F0.trans F1)⟩

/-- After the checks, the factors' values to `pre`. -/
theorem partB_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ u, B s₀ u → WP isa c u Q) :
    WP isa (.seq (.block (curBlock ++ setupP oBP oPLen)) (.seq (PrivPre.prime 4)
      (.seq (.block (setupP oBQ oQLen)) (.seq (PrivPre.prime 5) c)))) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have dcpL : cpL s₀ = (s₀.gpr .a5).toNat := rfl
  have dcqL : cqL s₀ = (s₀.gpr .a7).toNat := rfl
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dAQ : oAQ s₀ = slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have eX8 := e (cwX s₀) 8; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5
  have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  have eP24' := e (wordsOf (cpL s₀)) 24; have eQ24' := e (wordsOf (cqL s₀)) 24
  have eX8' := e (2 * ((ck s₀ + 7) / 8)) 8
  have wP2 : 2 ≤ cwP s₀ := two_le_wordsOf
  have wQ2 : 2 ≤ cwQ s₀ := two_le_wordsOf
  have wPX : cwP s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt pk) (by omega_arith)
  have wQX : cwQ s₀ ≤ cw s₀ := wordsOf_le_of (Nat.le_of_lt qk) (by omega_arith)
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  have hPS := hP.sepPre
  refine partBy_ok hP hA fun y Y => ?_
  have ty := Y.keep
  -- `q`'s values.
  refine WP.seq (WP.mono (prime_ok Y.pa hPS (by omega_arith) (by omega_arith)) fun z ⟨⟨zw, _, zF⟩, zk⟩ => ?_)
  have tz := ty.trans zk
  have hz : ∀ d, d + 8 ≤ slot (cwX s₀) 8 → d + 8 ≤ oDP ∨ oDP + 8 ≤ d →
      Mont.word z.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd hd' => by
    rw [frame_word zF hPS (by omega_arith) (by omega_arith) hd' (by omega_arith) hn hnP, Y.hdr d hd hd']
  have hscr_sub : ∀ {o n : Nat}, o + n ≤ cZ s₀ → Region.Sub ⟨Mont.off (cS s₀) o, n⟩ (scrR s₀) :=
    fun h => Offset.sub_base _ (by omega_arith)
  have F2 : Frame [preR s₀, scrR s₀] y.mem z.mem := zF.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨preR s₀, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub (by omega_arith)⟩
    · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub (by unfold oDP; omega_arith)⟩
  refine hc z ⟨hA.scr.congr tz.2.2, ?_, ?_, ?_, ?_, (tz.gpr (by decide)).trans hA.s6, fun i hi => ?_,
    fun i hi => ?_, (hA.keep.trans ty).trans zk, fun i hi => ?_, (hA.frame.trans Y.frame).trans F2⟩
  · rw [hz _ (by unfold oOut; omega_arith) (by unfold oOut oDP; omega_arith)]; exact hA.hOut
  · rw [hz _ (by unfold oN; omega_arith) (by unfold oN oDP; omega_arith)]; exact hA.hN
  · rw [hz _ (by unfold oNLen; omega_arith) (by unfold oNLen oDP; omega_arith)]; exact hA.hNL
  · rw [hz _ (by unfold oMask; omega_arith) (by unfold oMask oDP; omega_arith)]; exact hA.hMask
  · rw [frame_word_pre zF hPS (by omega_arith) (by omega_arith) (by omega_arith) (by unfold oDP; omega_arith) hnP
      (by omega_arith), Y.xw i hi, r2Word_mask]
  · rw [zw i hi, r2Word_mask]
  · have esav : off (savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [off, Mont.off, savW]; rw [Offset.add_add]
    have h1 := hA.sav i hi
    rw [esav] at h1 ⊢
    change Mont.word z.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [hz _ (by omega_arith) (by unfold oDP; omega_arith)]
    exact h1

end VG.Proof.Bignum.RISCV64.PrivPre
