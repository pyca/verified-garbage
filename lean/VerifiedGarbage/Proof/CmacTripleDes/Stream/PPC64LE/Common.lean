module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.CmacTripleDes.Bytes
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming TDEA-CMAC on PPC64LE: what the functions share

The weakest preconditions of the instructions `Framework/PPC64LE/Step.lean`
lacks (`mflr`, `mtlr`, `or`, `ldbrx`, `stdbrx`), the doubling of `dblCode`
(`dblCode_wp`), and that a word is determined by its bytes (`le8_inj`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE
open VG.Proof.Cmac (le8)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mflr {d : Reg} (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {r : Reg} (k : WP isa (.block is) { s with lr := s.gpr r } Q) :
    WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (rev64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t (rev64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]

end

/-- A slot of the working space at `B` is writable. -/
theorem scr_in {s : State} {B : Addr} {off : Nat} (hw : (⟨B, 640⟩ : Region) ∈ s.wr) (h : off + 8 ≤ 640) :
    InRegions s.wr (B + BitVec.ofNat 64 off) 8 :=
  ⟨_, hw, VG.Offset.contains_base _ h (by omega)⟩

theorem scr_rd {s : State} {B : Addr} {off : Nat} (hw : (⟨B, 640⟩ : Region) ∈ s.wr) (h : off + 8 ≤ 640) :
    InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 off) 8 :=
  let ⟨r, hr, hc⟩ := scr_in hw h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word read past a word written apart from it. -/
theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega)
    (by simp only [Region.Contains]; omega)) (by decide)

/-- The registers the functions use as temporaries are not preserved. -/
theorem preserved_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧
    r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem rev64_eq (x : BitVec 64) : rev64 x = byteRev64 x := rfl

theorem rev64_rev64 (x : BitVec 64) : rev64 (rev64 x) = x := Proof.Gcm.byteRev64_byteRev64 x

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- The doubling as `dblCode` computes it. -/
theorem dbl_eq (y : BitVec 64) :
    (y <<< 1) ^^^ ((0 - (y >>> 63)) &&& BitVec.ofNat 64 0x1b) = dbl64 y := by
  rw [msb_shift, dbl64]
  by_cases hm : y.msb
  · rw [ite_eq_left hm, ite_eq_left hm]; congr 1
  · rw [ite_eq_right hm, ite_eq_right hm]; congr 1

/-- `dblCode` doubles `r7`, with `r6 = 0`, writing `r8`–`r10`. -/
theorem dblCode_wp {s : State} {is : List Instr} {Q : State → Prop} (h6 : s.gpr .r6 = 0)
    (k : ∀ s', s'.gpr .r7 = dbl64 (s.gpr .r7) →
      (∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dblCode ++ is)) s Q := by
  simp only [dblCode, List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    wp_and fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_xor fun s₆ u₆ => ?_
  refine k s₆ ?_ (fun r h7 h8 h9 h10 => ?_) (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · have a5 : s₅.gpr .r7 = s.gpr .r7 <<< 1 := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    have b3 : s₃.gpr .r9 = 0 - (s.gpr .r7 >>> 63) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h6]
      rfl
    have b5 : s₅.gpr .r9 = (0 - (s.gpr .r7 >>> 63)) &&& BitVec.ofNat 64 0x1b := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, b3]
    rw [u₆.gpr, a5, b5, dbl_eq]
  · rw [u₆.other r h7, u₅.other r h7, u₄.other r h9, u₃.other r h10, u₂.other r h9, u₁.other r h8]

/-- `(n - 1) & 7`, plus one. -/
theorem held_word {n : Nat} (hn : n < 2 ^ 64) (h0 : n ≠ 0) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 &&& BitVec.ofNat 64 7) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 ((n - 1) % 8 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 n - BitVec.ofNat 64 1).toNat = n - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_add, BitVec.toNat_and, e1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]

/-- `heldCode` computes, from `count = n` in `r4`, the number of bytes held
back for a message of `n` bytes, to `r8`, through `r9`. -/
theorem heldCode_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h4 : s.gpr .r4 = BitVec.ofNat 64 n)
    {Q : State → Prop}
    (k : ∀ t, t.gpr .r8 = BitVec.ofNat 64 (Proof.CmacTripleDes.Stream.held n) →
      (∀ r, r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → Q t) :
    WP isa heldCode s Q := by
  by_cases h0 : n = 0
  · subst h0
    refine WP.ite true (by rw [eval_zero_ofNat s .r4 (by decide) h4]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_li (by decide) fun t u => wp_nil (k t (by rw [u.gpr]; rfl) (fun r h8 _ => u.other r h8) u.mem u.rd u.wr)
  refine WP.ite false (by rw [eval_zero_ofNat s .r4 hn h4]; simp [h0]) (fun h => by cases h) fun _ => ?_
  refine wp_subi (by decide) (by decide) fun t₁ u₁ => wp_li (by decide) fun t₂ u₂ => wp_and fun t₃ u₃ =>
    wp_addi (by decide) (by decide) fun t₄ u₄ => wp_nil ?_
  refine k t₄ ?_ (fun r h8 h9 => by rw [u₄.other r h8, u₃.other r h8, u₂.other r h9, u₁.other r h8])
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, h4, Proof.CmacTripleDes.Stream.held_pos (by omega)]
  exact held_word hn h0

end VG.Proof.CmacTripleDes.Stream.PPC64LE
