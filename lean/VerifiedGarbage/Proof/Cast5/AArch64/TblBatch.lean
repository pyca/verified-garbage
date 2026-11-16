module

public import VerifiedGarbage.Impl.Cast5.AArch64.Tbl
public import VerifiedGarbage.Proof.Blowfish.AArch64.Sbox
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Blowfish.AArch64.Round
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Cast5.AArch64.Run
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Blowfish.AArch64.Batch
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# CAST5 on AArch64: a batch of sixteen blocks, S-boxes by `tbl`

The proofs of `Impl/Cast5/AArch64/Tbl.lean`'s batch, in the order of the
code: the S-box lookups, one round, the rounds, and the batch (`batch_ok`).
-/

-- separate module: the batch, which CBC and CFB64 decryption are to run as the ECB functions do

@[expose] public section

/-!
## CAST5 on AArch64: S-box lookups by `tbl`

As Blowfish's (`Proof/Blowfish/AArch64/Sbox.lean`), with the planes in the
table of constants the loads carry (`ldrqTbl`) rather than in memory.

`quarter_run`: four loads of quarter `q` of byte plane `b` of S-box `j` into
`v28`–`v31`, then a `tbl` (for `q = 0`) or `tbx` of them, leave in each byte
lane of the destination the plane's byte at the lane's index, if it is in
the quarter (below 64), and otherwise 0 (`tbl`) or the destination's byte
(`tbx`). `lookupPlane_run`: the four quarters, on the index XORed with 0, 64,
128 and 192, leave the plane's byte at the index. `lookup_run`: `lookup j`
leaves in `outReg b` byte `b` of S-box `j` at the indices in `idxReg j`.
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planeOff)
open VG.AArch64.Tbl (VOnly)
open VG.Proof.Blowfish.AArch64 (vbyte_xor tbx_chain regs_ne repeat_succ_v28 exec_tbl4 Consts lookupRegs
  VOnly.mono q_notin idx_notin out_notin idx_ne_q123 plane_sub)

/-! ## The table -/

def sbox (j : Nat) (x : Byte) : Spec.Cast5.Word :=
  match j with
  | 0 => Spec.Cast5.S1 x
  | 1 => Spec.Cast5.S2 x
  | 2 => Spec.Cast5.S3 x
  | 3 => Spec.Cast5.S4 x
  | 4 => Spec.Cast5.S5 x
  | 5 => Spec.Cast5.S6 x
  | 6 => Spec.Cast5.S7 x
  | _ => Spec.Cast5.S8 x
def planeByte (o : Nat) : Byte :=
  (sbox (o / 1024) (BitVec.ofNat 8 o)).extractLsb' (8 * (o / 256 % 4)) 8

theorem getD_flatMap {α β : Type} (f : α → List β) (n : Nat) (d : β) (a0 : α) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = n) → ∀ i r, i < l.length → r < n →
      (l.flatMap f).getD (n * i + r) d = (f (l.getD i a0)).getD r d
  | [], _, i, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, hl, i, r, hi, hr => by
    rw [List.flatMap_cons, Proof.Cast5.getD_append', hl a List.mem_cons_self]
    cases i with
    | zero => rw [ite_eq_left (by omega), Nat.mul_zero, Nat.zero_add]; rfl
    | succ i =>
      rw [ite_eq_right (by rw [Nat.mul_succ]; omega), show n * (i + 1) + r - n = n * i + r by rw [Nat.mul_succ]; omega]
      exact getD_flatMap f n d a0 l (fun a ha => hl a (List.mem_cons_of_mem _ ha)) i r
        (by simpa using hi) hr

theorem getD_map {α β : Type} (g : α → β) (l : List α) (d : β) (a0 : α) {x : Nat} (hx : x < l.length) :
    (l.map g).getD x d = g (l.getD x a0) := by
  simp [List.getD_eq_getElem?_getD, hx]

theorem sbox_getD {j : Nat} (hj : j < 8) (o : Nat) :
    (sboxes.getD j []).getD (o % 256) 0 = sbox j (BitVec.ofNat 8 o) := by
  obtain hx : o % 256 < 256 := Nat.mod_lt _ (by decide)
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sboxes, sbox, Spec.Cast5.S1, Spec.Cast5.S2, Spec.Cast5.S3, Spec.Cast5.S4, Spec.Cast5.S5, Spec.Cast5.S6,
      Spec.Cast5.S7, Spec.Cast5.S8, List.getD_eq_getElem?_getD, hx]

theorem sboxes_len : ∀ s ∈ sboxes, s.length = 256 := by
  intro s hs
  simp only [sboxes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Vector.length_toList

theorem planeBytes_getD {o : Nat} (ho : o < 8192) : planeBytes.getD o 0 = planeByte o := by
  obtain e : o = 1024 * (o / 1024) + (256 * (o / 256 % 4) + o % 256) := by omega
  obtain hs : (sboxes.getD (o / 1024) []).length = 256 := by
    obtain hj : o / 1024 < 8 := by omega
    rcases (by omega : o / 1024 = 0 ∨ o / 1024 = 1 ∨ o / 1024 = 2 ∨ o / 1024 = 3 ∨ o / 1024 = 4 ∨ o / 1024 = 5 ∨
        o / 1024 = 6 ∨ o / 1024 = 7) with h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact Vector.length_toList
  rw [planeBytes]
  conv => lhs; rw [e]
  rw [getD_flatMap _ 1024 0 [] sboxes (fun s hs => by
      rw [List.length_flatMap]; simp [sboxes_len s hs]; rfl) _ _ (by show o / 1024 < 8; omega) (by omega),
    getD_flatMap _ 256 0 0 (List.range 4) (fun b _ => by rw [List.length_map, hs]) _ _ (by simp; omega)
      (Nat.mod_lt _ (by decide)),
    getD_map _ _ 0 0 (by rw [hs]; exact Nat.mod_lt _ (by decide)), sbox_getD (by omega), planeByte]
  simp [List.getD_eq_getElem?_getD, show o / 256 % 4 < 4 by omega]

theorem app_zero {w : Nat} (x : BitVec w) (b : BitVec 8) : (x ++ b).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi]

theorem app_succ {w : Nat} (x : BitVec w) (b : BitVec 8) (n : Nat) :
    (x ++ b).extractLsb' (n + 8) 8 = x.extractLsb' n 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, show ¬ n + 8 + i < 8 by omega, show n + 8 + i - 8 = n + i by omega]

theorem ext8 (x : BitVec 8) : x.extractLsb' 0 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem w8_byte (f : Nat → Byte) {k : Nat} (hk : k < 8) :
    (f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0 : BitVec 64).extractLsb' (8 * k) 8 = f k := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact app_zero _ _
  · exact (app_succ _ _ 0).trans (app_zero _ _)
  · exact (app_succ _ _ 8).trans ((app_succ _ _ 0).trans (app_zero _ _))
  · exact (app_succ _ _ 16).trans ((app_succ _ _ 8).trans ((app_succ _ _ 0).trans (app_zero _ _)))
  · exact (app_succ _ _ 24).trans ((app_succ _ _ 16).trans ((app_succ _ _ 8).trans ((app_succ _ _ 0).trans
      (app_zero _ _))))
  · exact (app_succ _ _ 32).trans ((app_succ _ _ 24).trans ((app_succ _ _ 16).trans ((app_succ _ _ 8).trans
      ((app_succ _ _ 0).trans (app_zero _ _)))))
  · exact (app_succ _ _ 40).trans ((app_succ _ _ 32).trans ((app_succ _ _ 24).trans ((app_succ _ _ 16).trans
      ((app_succ _ _ 8).trans ((app_succ _ _ 0).trans (app_zero _ _))))))
  · exact (app_succ _ _ 48).trans ((app_succ _ _ 40).trans ((app_succ _ _ 32).trans ((app_succ _ _ 24).trans
      ((app_succ _ _ 16).trans ((app_succ _ _ 8).trans ((app_succ _ _ 0).trans (ext8 _)))))))

theorem pack_getD : ∀ (i : Nat) (l : List Byte), 8 * (i + 1) ≤ l.length →
    (pack l).getD i 0 = (l.getD (8 * i + 7) 0 ++ l.getD (8 * i + 6) 0 ++ l.getD (8 * i + 5) 0 ++
      l.getD (8 * i + 4) 0 ++ l.getD (8 * i + 3) 0 ++ l.getD (8 * i + 2) 0 ++ l.getD (8 * i + 1) 0 ++
      l.getD (8 * i) 0 : BitVec 64)
  | i, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h => by
    cases i with
    | zero => rfl
    | succ i =>
      have := pack_getD i rest (by simp at h; omega)
      rw [pack, List.getD_cons_succ, this]
      obtain e : ∀ k, (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).getD (8 * (i + 1) + k) 0 =
          rest.getD (8 * i + k) 0 := fun k => by
        rw [show 8 * (i + 1) + k = (8 * i + k) + 8 by omega]; rfl
      rw [e 7, e 6, e 5, e 4, e 3, e 2, e 1, show 8 * (i + 1) = 8 * (i + 1) + 0 from rfl, e 0]
      rfl
  | _, [], h => by simp at h
  | _, [_], h => by simp at h; omega
  | _, [_, _], h => by simp at h; omega
  | _, [_, _, _], h => by simp at h; omega
  | _, [_, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _, _], h => by simp at h; omega
  | _, [_, _, _, _, _, _, _], h => by simp at h; omega

theorem planeBytes_length : planeBytes.length = 8192 := by
  rw [planeBytes, List.length_flatMap]
  have : ∀ s ∈ sboxes, ((List.range 4).flatMap fun b => s.map fun w => w.extractLsb' (8 * b) 8).length = 1024 := by
    intro s hs; rw [List.length_flatMap]; simp [sboxes_len s hs]; rfl
  rw [List.map_congr_left this]; rfl

theorem vbyte_app (hi lo : BitVec 64) {e : Nat} (he : e < 16) :
    vbyte (hi ++ lo) e = if e < 8 then lo.extractLsb' (8 * e) 8 else hi.extractLsb' (8 * (e - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  by_cases h : e < 8
  · simp [h, hi', show 8 * e + i < 64 by omega]
  · simp [h, hi', show ¬ 8 * e + i < 64 by omega, show 8 * e + i - 64 = 8 * (e - 8) + i by omega]

theorem vbyte_pld {o : Nat} (ho : o % 16 = 0 ∧ o + 16 ≤ 8192) {e : Nat} (he : e < 16) :
    vbyte (planeWords.getD (o / 8 + 1) 0 ++ planeWords.getD (o / 8) 0) e = planeByte (o + e) := by
  rw [vbyte_app _ _ he, planeWords, pack_getD _ _ (by rw [planeBytes_length]; omega),
    pack_getD _ _ (by rw [planeBytes_length]; omega)]
  by_cases h : e < 8
  · have w := w8_byte (fun k => planeBytes.getD (8 * (o / 8) + k) 0) h
    simp only [Nat.add_zero] at w
    rw [ite_eq_left h, w, planeBytes_getD (by omega)]
    exact congrArg planeByte (by omega)
  · have w := w8_byte (fun k => planeBytes.getD (8 * (o / 8 + 1) + k) 0) (show e - 8 < 8 by omega)
    simp only [Nat.add_zero] at w
    rw [ite_eq_right h, w, planeBytes_getD (by omega)]
    exact congrArg planeByte (by omega)

theorem pack_length : ∀ l : List Byte, (pack l).length = l.length / 8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => by
    rw [pack, List.length_cons, pack_length rest]
    simp only [List.length_cons]
    omega
  | [] => rfl
  | [_] => by simp [pack]
  | [_, _] => by simp [pack]
  | [_, _, _] => by simp [pack]
  | [_, _, _, _] => by simp [pack]
  | [_, _, _, _, _] => by simp [pack]
  | [_, _, _, _, _, _] => by simp [pack]
  | [_, _, _, _, _, _, _] => by simp [pack]

theorem planeWords_length : planeWords.length = 1024 := by
  rw [planeWords, pack_length, planeBytes_length]

/-- What a load of the table's sixteen bytes at `o` leaves. -/
def pldV (o : Nat) : BitVec 128 := planeWords.getD (o / 8 + 1) 0 ++ planeWords.getD (o / 8) 0

/-- A load of the table's sixteen bytes at `off`. -/
theorem exec_pld (s : State) (t : VReg) {off : Nat} (ho : off % 16 = 0 ∧ off + 16 ≤ 8192)
    (h9 : s.gpr .x9 = s.syms planesSym) :
    exec (.ldrqTbl t .x9 off planesSym planeWords) s = some (s.setV t (pldV off)) := by
  obtain hc : s.gpr .x9 = s.syms planesSym ∧ off % 16 = 0 ∧ off < 65536 ∧ off / 8 + 2 ≤ planeWords.length := by
    rw [planeWords_length]; exact ⟨h9, ho.1, by omega_using [ho], by omega_using [ho]⟩
  change (if _ then _ else _) = _
  rw [ite_eq_left hc]
  rfl

/-- Byte `b` of S-box `j` at `x`. -/
theorem planeByte_eq {j b : Nat} (hj : j < 8) (hb : b < 4) (x : Byte) :
    planeByte (planeOff j b + x.toNat) = (sbox j x).extractLsb' (8 * b) 8 := by
  have hx := x.isLt
  obtain e1 : (planeOff j b + x.toNat) / 1024 = j := by simp only [planeOff]; omega_arith
  obtain e2 : (planeOff j b + x.toNat) / 256 % 4 = b := by simp only [planeOff]; omega_arith
  obtain e3 : BitVec.ofNat 8 (planeOff j b + x.toNat) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]; simp only [planeOff]; omega_arith
  rw [planeByte, e1, e2, e3]

/-! ## A quarter -/

theorem loadQuarter_eq (j b q : Nat) :
    loadQuarter j b q =
      [.ldrqTbl .v28 .x9 (planeOff j b + 64 * q + 16 * 0) planesSym planeWords,
       .ldrqTbl .v29 .x9 (planeOff j b + 64 * q + 16 * 1) planesSym planeWords,
       .ldrqTbl .v30 .x9 (planeOff j b + 64 * q + 16 * 2) planesSym planeWords,
       .ldrqTbl .v31 .x9 (planeOff j b + 64 * q + 16 * 3) planesSym planeWords] :=
  rfl

theorem quarter_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) {j b q : Nat} (hj : j < 8)
    (hb : b < 4) (hq : q < 4) {d m : VReg} (hd : ∀ r < 4, d ≠ tReg r) (hm : ∀ r < 4, m ≠ tReg r) :
    ∃ s', runBlock isa (loadQuarter j b q ++ ([.vop (.tblN (q != 0) 4 d (tReg 0) m)] : List Instr)) s = some s' ∧
      (∀ e < 16, vbyte (s'.v d) e =
        if (vbyte (s.v m) e).toNat < 64 then
          planeByte (planeOff j b + 64 * q + (vbyte (s.v m) e).toNat)
        else if q != 0 then vbyte (s.v d) e else 0) ∧
      VOnly [.v28, .v29, .v30, .v31, d] s s' := by
  let base := planeOff j b + 64 * q
  obtain hbase : base % 16 = 0 ∧ base + 64 ≤ 8192 := by simp only [base, planeOff]; omega_arith
  let ld (r : Nat) := pldV (base + 16 * r)
  let s₁ := s.setV .v28 (ld 0)
  let s₂ := s₁.setV .v29 (ld 1)
  let s₃ := s₂.setV .v30 (ld 2)
  let s₄ := s₃.setV .v31 (ld 3)
  obtain hv : ∀ r < 4, s₄.v (tReg r) = ld r := by
    intro r hr
    rcases (by omega_arith : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl
  obtain hv' : ∀ x, (∀ r < 4, x ≠ tReg r) → s₄.v x = s.v x := by
    intro x hx
    obtain h0 : x ≠ .v28 := hx 0 (by decide)
    obtain h1 : x ≠ .v29 := hx 1 (by decide)
    obtain h2 : x ≠ .v30 := hx 2 (by decide)
    obtain h3 : x ≠ .v31 := hx 3 (by decide)
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2,
      v_setV_of_ne _ _ h3]
  let s₅ := s₄.setV d (ofVBytes fun i =>
      if (vbyte (s₄.v m) i).toNat < 16 * 4 then tableByte s₄.v (tReg 0) (vbyte (s₄.v m) i).toNat
      else if (q != 0) then vbyte (s₄.v d) i else 0)
  obtain ho : ∀ r < 4, (base + 16 * r) % 16 = 0 ∧ base + 16 * r + 16 ≤ 8192 := fun r hr => by
    omega_using [hbase, hr]
  refine ⟨s₅, ?_, ?_, ?_⟩
  · have e₁ : exec (.ldrqTbl .v28 .x9 (planeOff j b + 64 * q + 16 * 0) planesSym planeWords) s = some s₁ :=
      exec_pld s _ (ho 0 (by decide)) h9
    obtain e₂ : exec (.ldrqTbl .v29 .x9 (planeOff j b + 64 * q + 16 * 1) planesSym planeWords) s₁ = some s₂ :=
      exec_pld s₁ _ (ho 1 (by decide)) h9
    obtain e₃ : exec (.ldrqTbl .v30 .x9 (planeOff j b + 64 * q + 16 * 2) planesSym planeWords) s₂ = some s₃ :=
      exec_pld s₂ _ (ho 2 (by decide)) h9
    obtain e₄ : exec (.ldrqTbl .v31 .x9 (planeOff j b + 64 * q + 16 * 3) planesSym planeWords) s₃ = some s₄ :=
      exec_pld s₃ _ (ho 3 (by decide)) h9
    obtain e₅ : exec (.vop (.tblN (q != 0) 4 d (tReg 0) m)) s₄ = some s₅ := exec_tbl4 _ _ _ _ _
    rw [loadQuarter_eq]
    simp only [List.cons_append, List.nil_append]
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · intro e he
    simp only [s₅, v_setV_self]
    rw [vbyte_ofVBytes _ he, hv' m hm, hv' d hd]
    split
    · rename_i h
      rw [tableByte, repeat_succ_v28 _ (by omega_arith), hv _ (by omega_arith)]
      exact (vbyte_pld (ho _ (by omega_arith)) (Nat.mod_lt _ (by decide))).trans
        (congrArg planeByte (by omega_using [hbase, h]))
    · rfl
  · refine ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-! ## A byte plane -/

theorem lookupPlane_eq (t j b : Nat) :
    lookupPlane t j b =
      (loadQuarter t b 0 ++ ([.vop (.tblN (0 != 0) 4 (outReg b) (tReg 0) (idxReg j))] : List Instr)) ++
      ((loadQuarter t b 1 ++ ([.vop (.tblN (1 != 0) 4 (outReg b) (tReg 0) (qReg 1))] : List Instr)) ++
      ((loadQuarter t b 2 ++ ([.vop (.tblN (2 != 0) 4 (outReg b) (tReg 0) (qReg 2))] : List Instr)) ++
      ((loadQuarter t b 3 ++ ([.vop (.tblN (3 != 0) 4 (outReg b) (tReg 0) (qReg 3))] : List Instr)) ++ []))) :=
  rfl

/-- Byte plane `b` of S-box `j`, at the indices in `idxReg j` (and them
XORed with 64, 128 and 192 in `qReg`). -/
theorem lookupPlane_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) {t j b : Nat} (ht : t < 8) (hj : j < 4)
    (hb : b < 4) (hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s.v (qReg q)) e = vbyte (s.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) :
    ∃ s', runBlock isa (lookupPlane t j b) s = some s' ∧
      (∀ e < 16, vbyte (s'.v (outReg b)) e = planeByte (planeOff t b + (vbyte (s.v (idxReg j)) e).toNat)) ∧
      VOnly [.v28, .v29, .v30, .v31, outReg b] s s' := by
  obtain ne := regs_ne j hj b hb
  obtain hd : ∀ r < 4, outReg b ≠ tReg r := fun r hr => (ne 0 (by decide) r hr).1
  obtain h9' : ∀ {u : State}, VOnly [.v28, .v29, .v30, .v31, outReg b] s u → u.gpr .x9 = u.syms planesSym := by
    intro u hu
    rw [hu.gpr, hu.1]; exact h9
  obtain ⟨s₁, r₁, v₁, o₁⟩ := quarter_run h9 ht hb (by decide : 0 < 4) hd (fun r hr => (ne 0 (by decide) r hr).2.1)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := quarter_run (h9' o₁) ht hb (by decide : 1 < 4) hd
    (fun r hr => (ne 1 (by decide) r hr).2.2.1)
  obtain o₁₂ := o₁.trans o₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := quarter_run (h9' o₁₂) ht hb (by decide : 2 < 4) hd
    (fun r hr => (ne 2 (by decide) r hr).2.2.1)
  obtain o₁₃ := o₁₂.trans o₃
  obtain ⟨s₄, r₄, v₄, o₄⟩ := quarter_run (h9' o₁₃) ht hb (by decide : 3 < 4) hd
    (fun r hr => (ne 3 (by decide) r hr).2.2.1)
  obtain o₁₄ := o₁₃.trans o₄
  refine ⟨s₄, ?_, ?_, o₁₄⟩
  · rw [lookupPlane_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₁ (VG.AArch64.Tbl.runBlock_cat_some r₂
      (VG.AArch64.Tbl.runBlock_cat_some r₃ (VG.AArch64.Tbl.runBlock_cat_some r₄ runBlock_nil)))
  · intro e he
    obtain kept : ∀ {u : State} (x : VReg), VOnly [.v28, .v29, .v30, .v31, outReg b] s u →
        (∀ r < 4, x ≠ tReg r) → x ≠ outReg b → u.v x = s.v x := by
      intro u x hu hx hxo
      refine hu.2 x ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have := hx 0 (by decide); have := hx 1 (by decide); have := hx 2 (by decide)
      have := hx 3 (by decide)
      rintro (h | h | h | h | h) <;> contradiction
    obtain q₁ : s₁.v (qReg 1) = s.v (qReg 1) := kept _ o₁ (fun r hr => (ne 1 (by decide) r hr).2.2.1)
      (ne 1 (by decide) 0 (by decide)).2.2.2.2.1
    obtain q₂ : s₂.v (qReg 2) = s.v (qReg 2) := kept _ o₁₂ (fun r hr => (ne 2 (by decide) r hr).2.2.1)
      (ne 2 (by decide) 0 (by decide)).2.2.2.2.1
    obtain q₃ : s₃.v (qReg 3) = s.v (qReg 3) := kept _ o₁₃ (fun r hr => (ne 3 (by decide) r hr).2.2.1)
      (ne 3 (by decide) 0 (by decide)).2.2.2.2.1
    let X := vbyte (s.v (idxReg j)) e
    have hX : X.toNat < 256 := X.isLt
    obtain hxq : ∀ q < 4, 0 < q → (vbyte (s.v (qReg q)) e).toNat = X.toNat ^^^ 64 * q := by
      intro q hq0 hq1
      rw [hq q hq0 hq1 e he, VG.AArch64.Tbl.toNat_xor_lit _ _ (by omega_arith)]
    rw [v₄ e he, q₃, hxq 3 (by decide) (by decide), v₃ e he, q₂, hxq 2 (by decide) (by decide),
      v₂ e he, q₁, hxq 1 (by decide) (by decide), v₁ e he]
    simp only [show (3 != 0) = true from rfl, show (2 != 0) = true from rfl,
      show (1 != 0) = true from rfl, show (0 != 0) = false from rfl, ite_true, Bool.false_eq_true,
      ite_false]
    have := tbx_chain (fun i => planeByte (planeOff t b + i)) X.toNat hX
    simp only [Nat.add_assoc]
    exact this

/-! ## An S-box -/

theorem lookup_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) {t j : Nat} (ht : t < 8)
    (hj : j < 4) :
    ∃ s', runBlock isa (lookup t j) s = some s' ∧
      (∀ b < 4, ∀ e < 16, vbyte (s'.v (outReg b)) e =
        (sbox t (vbyte (s.v (idxReg j)) e)).extractLsb' (8 * b) 8) ∧
      VOnly lookupRegs s s' := by
  obtain hidx := idx_ne_q123 j hj
  let s₁ := s.setV (qReg 1) (s.v (idxReg j) ^^^ s.v c64)
  let s₂ := s₁.setV (qReg 2) (s₁.v (idxReg j) ^^^ s₁.v c128)
  let s₃ := s₂.setV (qReg 3) (s₂.v (qReg 1) ^^^ s₂.v c128)
  obtain X : s₃.v (idxReg j) = s.v (idxReg j) := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV_of_ne _ _ hidx.1,
      v_setV_of_ne _ _ hidx.2.1, v_setV_of_ne _ _ hidx.2.2]
  obtain q1 : s₃.v (qReg 1) = s.v (idxReg j) ^^^ s.v c64 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false]
  obtain q2 : s₃.v (qReg 2) = s.v (idxReg j) ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  obtain q3 : s₃.v (qReg 3) = s.v (idxReg j) ^^^ s.v c64 ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  obtain hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s₃.v (qReg q)) e = vbyte (s₃.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q) := by
    intro q hq0 hq1 e he
    rw [X]
    rcases (by omega_using [hq0, hq1] : q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl
    · rw [q1, vbyte_xor, hc.1 e he]; rfl
    · rw [q2, vbyte_xor, hc.2 e he]; rfl
    · rw [q3, vbyte_xor, vbyte_xor, hc.1 e he, hc.2 e he, BitVec.xor_assoc]; rfl
  obtain o₃ : VOnly lookupRegs s s₃ :=
    (((VOnly.setV s (by simp [lookupRegs, qReg]) _).trans (VOnly.setV _ (by simp [lookupRegs, qReg]) _)).trans
      (VOnly.setV _ (by simp [lookupRegs, qReg]) _))
  obtain h9₃ : ∀ {u : State}, VOnly lookupRegs s u → u.gpr .x9 = u.syms planesSym := by
    intro u hu
    rw [hu.gpr, hu.1]; exact h9
  obtain step : ∀ {u : State} (b : Nat), b < 4 → VOnly lookupRegs s u →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (u.v (qReg q)) e = vbyte (u.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      ∃ u', runBlock isa (lookupPlane t j b) u = some u' ∧
        (∀ e < 16, vbyte (u'.v (outReg b)) e = planeByte (planeOff t b + (vbyte (u.v (idxReg j)) e).toNat)) ∧
        VOnly [.v28, .v29, .v30, .v31, outReg b] u u' := by
    intro u b hb hu hqt
    exact lookupPlane_run (h9₃ hu) ht hj hb hqt
  have ob := plane_sub
  obtain hqk : ∀ {u u' : State} (b : Nat), b < 4 → VOnly [.v28, .v29, .v30, .v31, outReg b] u u' →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (u.v (qReg q)) e = vbyte (u.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (u'.v (qReg q)) e = vbyte (u'.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) := by
    intro u u' b hb o h q hq0 hq1 e he
    rw [o.2 _ (q_notin q hq0 hq1 b hb), o.2 _ (idx_notin j hj b hb)]; exact h q hq0 hq1 e he
  obtain ni := idx_notin j hj
  obtain ⟨t₀, r₀, v₀, o₀⟩ := step 0 (by decide) o₃ hq
  obtain p₀ := o₃.trans (VOnly.mono o₀ (ob 0 (by decide)))
  obtain ⟨t₁, r₁, v₁, o₁⟩ := step 1 (by decide) p₀ (hqk 0 (by decide) o₀ hq)
  obtain p₁ := p₀.trans (VOnly.mono o₁ (ob 1 (by decide)))
  obtain ⟨t₂, r₂, v₂, o₂⟩ := step 2 (by decide) p₁ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq))
  obtain p₂ := p₁.trans (VOnly.mono o₂ (ob 2 (by decide)))
  obtain ⟨t₃, r₃, v₃, o₃'⟩ := step 3 (by decide) p₂
    (hqk 2 (by decide) o₂ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq)))
  obtain p₃ := p₂.trans (VOnly.mono o₃' (ob 3 (by decide)))
  refine ⟨t₃, ?_, ?_, p₃⟩
  · have e₁ : exec (veor (qReg 1) (idxReg j) c64) s = some s₁ := rfl
    have e₂ : exec (veor (qReg 2) (idxReg j) c128) s₁ = some s₂ := rfl
    have e₃ : exec (veor (qReg 3) (qReg 1) c128) s₂ = some s₃ := rfl
    have l : lookup t j = [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128,
        veor (qReg 3) (qReg 1) c128] ++ (lookupPlane t j 0 ++ (lookupPlane t j 1 ++
        (lookupPlane t j 2 ++ (lookupPlane t j 3 ++ [])))) := rfl
    rw [l, List.cons_append, List.cons_append, List.cons_append, List.nil_append, runBlock_cons, e₁,
      runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · have i₀ : t₀.v (idxReg j) = s.v (idxReg j) := (o₀.2 _ (ni 0 (by decide))).trans X
    obtain i₁ : t₁.v (idxReg j) = s.v (idxReg j) := (o₁.2 _ (ni 1 (by decide))).trans i₀
    obtain i₂ : t₂.v (idxReg j) = s.v (idxReg j) := (o₂.2 _ (ni 2 (by decide))).trans i₁
    intro b hb e he
    have nob := out_notin
    rw [← planeByte_eq ht hb]
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · rw [o₃'.2 _ (nob 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (nob 0 (by decide) 1 (by decide) (by decide)), v₀ e he, X]
    · rw [o₃'.2 _ (nob 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 1 (by decide) 2 (by decide) (by decide)),
        v₁ e he, i₀]
    · rw [o₃'.2 _ (nob 2 (by decide) 3 (by decide) (by decide)), v₂ e he, i₁]
    · rw [v₃ e he, i₂]

end VG.Proof.Cast5.AArch64.Tbl

/-!
## CAST5 on AArch64: one round on sixteen blocks

`round_ok`: `round t up`, with `x5` at `Kmᵢ` in the subkeys, for a round `i`
of Type `t`, leaves `R` in `A` and `L ^ f(R, Kmᵢ, Krᵢ)` in `B`, word by
word, and moves `x5` to the next subkey (`up`) or the previous one.
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planeOff
  planes words wordReg)
open VG.AArch64.Tbl (VOnly)
open VG.Spec.Cast5 (Word)

/-! ## Words -/

def opEval (o : Op) (a b : Word) : Word :=
  match o with
  | .add => a + b
  | .eor => a ^^^ b
  | .sub => a - b

/-- `f`'s accumulation through S-box `j`, for a round of Type `t` on `I = i`. -/
def fAcc (t : Nat) (i : Word) : Nat → Word
  | 0 => sbox 0 (Spec.Cast5.byte i 0)
  | j + 1 => opEval (op t (j + 1)) (fAcc t i j) (sbox (j + 1) (Spec.Cast5.byte i (j + 1)))

/-- §2.2's `f` of round `i`, of Type `t`. -/
theorem f_eq_fAcc {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hi : i % 3 = t % 3) (d km kr : Word) :
    Spec.Cast5.f i d km kr = fAcc t ((opEval (op t 0) km d).rotateLeft (kr.toNat % 32)) 3 := by
  rcases ht with rfl | rfl | rfl
  · have : i % 3 = 1 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 2 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 0 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]

theorem byte_eq (i : Word) (j : Nat) : Spec.Cast5.byte i j = i.extractLsb' (8 * (3 - j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [Spec.Cast5.byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hk,
    decide_true, Bool.true_and]

/-- The rotation, as the halves of a 64-bit product by a power of two. -/
theorem one_rot : ∀ r < 32, ((1 : Word).rotateLeft r).setWidth 64 = BitVec.twoPow 64 r := by decide
theorem rot_mul (x : Word) {r : Nat} (hr : r < 32) :
    (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 0 32 |||
      (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 32 32 = x.rotateLeft r := by
  rw [one_rot r hr, BitVec.mul_twoPow_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [Proof.Cast5.getLsbD_rotateLeft_lt _ hr hk, BitVec.getLsbD_or, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth]
  obtain h2 : 32 + k < 64 := by omega
  simp only [hk, h2, decide_true, Bool.true_and, Nat.zero_add]
  by_cases hkr : k < r
  · have e : 32 + k - r = 32 - r + k := by omega
    obtain h3 : ¬ 32 + k < r := by omega
    obtain h4 : 32 - r + k < 64 := by omega
    simp [show k < 64 by omega, hkr, h3, e, h4]
  · have h3 : ¬ 32 + k < r := by omega
    obtain h5 : k - r < 64 := by omega
    obtain h6 : x.getLsbD (32 + k - r) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [show k < 64 by omega, hkr, h3, h5, h6]
theorem vword_ofVDwords (a b : BitVec 64) {k : Nat} (hk : k < 4) :
    vword (ofVDwords a b) k = (if k < 2 then a else b).extractLsb' (32 * (k % 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [vword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and] <;>
    simp <;> (try split) <;> first | omega | rfl | (congr 1; omega)

theorem vword_or (x y : BitVec 128) (e : Nat) : vword (x ||| y) e = vword x e ||| vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

/-! ## What a step keeps -/

/-- Only the general-purpose registers `gs` and the vector registers `vs`
(and the flags) change. -/
structure RFrame (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem RFrame.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : RFrame gs vs a b)
    (h₂ : RFrame gs vs b c) : RFrame gs vs a c :=
  ⟨fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr),
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.syms.trans h₁.syms⟩

theorem RFrame.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : RFrame gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : RFrame gs' vs' a b :=
  ⟨fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h'), h.mem, h.rd, h.wr,
    h.sp, h.syms⟩

theorem RFrame.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : RFrame [] vs a b := by
  refine ⟨fun r _ => ?_, h.2, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h.1]

theorem vmono {ds ds' : List VReg} {a b : State} (h : VOnly ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    VOnly ds' a b := Proof.Blowfish.AArch64.VOnly.mono h hs

/-! ## Four registers, one instruction each -/

/-- Four instructions, instruction `k` writing `D k` with a value `g k` that
reads, of the registers `D`, at most `D k`. -/
theorem map4_run (s : State) (ins : Nat → Instr) (D : Nat → VReg)
    (g : Nat → (VReg → BitVec 128) → BitVec 128)
    (he : ∀ k < 4, ∀ u : State, exec (ins k) u = some (u.setV (D k) (g k u.v)))
    (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → D k ≠ D k')
    (hg : ∀ k < 4, ∀ v v' : VReg → BitVec 128, (∀ r, (∀ k' < 4, k' ≠ k → r ≠ D k') → v' r = v r) →
      g k v' = g k v) :
    ∃ s', runBlock isa ((List.range 4).map ins) s = some s' ∧ (∀ k < 4, s'.v (D k) = g k s.v) ∧
      VOnly [D 0, D 1, D 2, D 3] s s' := by
  let s₁ := s.setV (D 0) (g 0 s.v)
  let s₂ := s₁.setV (D 1) (g 1 s₁.v)
  let s₃ := s₂.setV (D 2) (g 2 s₂.v)
  let s₄ := s₃.setV (D 3) (g 3 s₃.v)
  have hl : (List.range 4).map ins = [ins 0, ins 1, ins 2, ins 3] := rfl
  obtain ne := fun k hk k' hk' (h : k ≠ k') => hinj k hk k' hk' h
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, he 0 (by decide), runStep_some, runBlock_cons, he 1 (by decide), runStep_some,
      runBlock_cons, he 2 (by decide), runStep_some, runBlock_cons, he 3 (by decide), runStep_some,
      runBlock_nil]
  · intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 1 (by decide) (by decide))]
      exact v_setV_self _ _ _
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 1 (by decide) _ _ fun r hr => v_setV_of_ne _ _ (hr 0 (by decide) (by decide))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 2 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 2 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide)))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 3 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 2 (by decide) (by decide))).trans
          ((v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide))))
  · exact (((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-! ## The operations -/

/-- An operation on the four words of two vectors. -/
def opV (o : Op) (x y : BitVec 128) : BitVec 128 :=
  match o with
  | .add => VArr.s4.map2 (fun _ a b => a + b) x y
  | .eor => x ^^^ y
  | .sub => VArr.s4.map2 (fun _ a b => a - b) x y

theorem exec_op (o : Op) (s : State) (d n m : VReg) :
    exec (o.instr d n m) s = some (s.setV d (opV o (s.v n) (s.v m))) := by
  cases o
  · exact (rfl : exec (.vop (.add .s4 d n m)) s = _)
  · exact (rfl : exec (veor d n m) s = _)
  · exact (rfl : exec (.vop (.sub .s4 d n m)) s = _)

theorem vword_opV (o : Op) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (opV o x y) l = opEval o (vword x l) (vword y l) := by
  cases o
  · show vword (VArr.s4.map2 (fun _ a b => a + b) x y) l = vword x l + vword y l
    rw [vword_map2 _ x y hl]
  · exact Proof.Blowfish.AArch64.vword_xor x y l
  · show vword (VArr.s4.map2 (fun _ a b => a - b) x y) l = vword x l - vword y l
    rw [vword_map2 _ x y hl]

/-! ## `f` -/

open VG.Proof.Blowfish.AArch64 (lane planes_run words_run word_ext vbyte_word lookupRegs wordsRegs fRegs
  stepRegs planesRegs halfRegs Consts fReg_notin idx_notin_step const_notin_step wordReg_ne_fReg fReg_ne)

/-- What `combine t j` does to a register of `f` and a register of words. -/
def cop (t j : Nat) (x y : BitVec 128) : BitVec 128 := if j = 0 then y else opV (op t j) x y

theorem vword_cop (t j : Nat) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (cop t j x y) l = if j = 0 then vword y l else opEval (op t j) (vword x l) (vword y l) := by
  simp only [cop]
  split
  · rfl
  · exact vword_opV _ x y hl

theorem combine_run (s : State) (t j : Nat) :
    ∃ s', runBlock isa (combine t j) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = cop t j (s.v (fReg k)) (s.v (wordReg k))) ∧ VOnly fRegs s s' := by
  refine map4_run s (fun k => if j = 0 then .vop (.mov (fReg k) (wordReg k))
      else (op t j).instr (fReg k) (fReg k) (wordReg k)) fReg
    (fun k v => cop t j (v (fReg k)) (v (wordReg k))) (fun k _ u => ?_) fReg_ne (fun k hk v v' h => ?_)
  · simp only [cop]
    split
    · rfl
    · exact exec_op _ _ _ _ _
  · show cop t j (v' (fReg k)) (v' (wordReg k)) = cop t j (v (fReg k)) (v (wordReg k))
    rw [h (fReg k) fun k' hk' hne => fReg_ne k hk k' hk' (Ne.symm hne),
      h (wordReg k) fun k' hk' _ => wordReg_ne_fReg k hk k' hk']

theorem sbox_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) {j : Nat} (hj : j < 4)
    (t : Nat) (x : Nat → Word) (hx : ∀ n < 16, vbyte (s.v (idxReg j)) n = Spec.Cast5.byte (x n) j)
    (hprev : 0 < j → ∀ n < 16, lane s.v fReg n = fAcc t (x n) (j - 1)) :
    ∃ s', runBlock isa (lookup j j ++ words ++ combine t j) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = fAcc t (x n) j) ∧ VOnly stepRegs s s' := by
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run h9 hc (t := j) (by omega_using [hj]) hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := combine_run s₂ t j
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_, ?_⟩
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain hl : n % 4 < 4 := by omega_using []
    obtain w : vword (s₂.v (wordReg (n / 4))) (n % 4) = sbox j (Spec.Cast5.byte (x n) j) := by
      refine word_ext fun b hb => ?_
      rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega_using [], v₁ _ hb _ hn, hx n hn]
    obtain f₂ : s₂.v (fReg (n / 4)) = s.v (fReg (n / 4)) := by
      rw [o₂.2 _ (fReg_notin _ hk).2, o₁.2 _ (fReg_notin _ hk).1]
    simp only [lane]
    rw [v₃ _ hk, vword_cop _ _ _ _ hl, w, f₂]
    rcases j with _ | j'
    · rfl
    · have hp := hprev (Nat.succ_pos _) n hn
      simp only [lane, Nat.add_sub_cancel] at hp
      rw [ite_eq_right (Nat.succ_ne_zero _), hp]
      rfl
  · exact ((Proof.Blowfish.AArch64.VOnly.mono o₁ (by decide)).trans (Proof.Blowfish.AArch64.VOnly.mono o₂ (by decide))).trans
      (Proof.Blowfish.AArch64.VOnly.mono o₃ (by decide))

theorem f_eq (t : Nat) :
    f t = (lookup 0 0 ++ words ++ combine t 0) ++ ((lookup 1 1 ++ words ++ combine t 1) ++
      ((lookup 2 2 ++ words ++ combine t 2) ++ ((lookup 3 3 ++ words ++ combine t 3) ++ []))) := rfl

/-- `f`'s S-boxes and operations, of sixteen words whose byte planes are in `idxReg`. -/
theorem f_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) (t : Nat) (x : Nat → Word)
    (hx : ∀ j < 4, ∀ n < 16, vbyte (s.v (idxReg j)) n = Spec.Cast5.byte (x n) j) :
    ∃ s', runBlock isa (f t) s = some s' ∧ (∀ n < 16, lane s'.v fReg n = fAcc t (x n) 3) ∧
      VOnly stepRegs s s' := by
  obtain keep : ∀ {u : State}, VOnly stepRegs s u →
      u.gpr .x9 = u.syms planesSym ∧ Consts u ∧
        (∀ j < 4, ∀ n < 16, vbyte (u.v (idxReg j)) n = Spec.Cast5.byte (x n) j) := by
    intro u hu
    refine ⟨by rw [hu.gpr, hu.1]; exact h9, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj n hn => ?_⟩
    · rw [hu.2 _ const_notin_step.1]; exact hc.1 e he
    · rw [hu.2 _ const_notin_step.2]; exact hc.2 e he
    · rw [hu.2 _ (idx_notin_step j hj)]; exact hx j hj n hn
  obtain ⟨s₀, r₀, v₀, o₀⟩ := sbox_run h9 hc (by decide : 0 < 4) t x (hx 0 (by decide)) (by intro h; omega)
  obtain k₀ := keep o₀
  obtain ⟨s₁, r₁, v₁, o₁⟩ := sbox_run k₀.1 k₀.2.1 (by decide : 1 < 4) t x (k₀.2.2 1 (by decide))
    (fun _ n hn => v₀ n hn)
  obtain p₁ := o₀.trans o₁
  obtain k₁ := keep p₁
  obtain ⟨s₂, r₂, v₂, o₂⟩ := sbox_run k₁.1 k₁.2.1 (by decide : 2 < 4) t x (k₁.2.2 2 (by decide))
    (fun _ n hn => v₁ n hn)
  obtain p₂ := p₁.trans o₂
  obtain k₂ := keep p₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := sbox_run k₂.1 k₂.2.1 (by decide : 3 < 4) t x (k₂.2.2 3 (by decide))
    (fun _ n hn => v₂ n hn)
  refine ⟨s₃, ?_, v₃, p₂.trans o₃⟩
  rw [f_eq]
  exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
    (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))

/-! ## The rotation -/

open VG.Proof.Blowfish.AArch64 (vword_uzp1 vword_uzp2 exec_vperm exec_vmov)

/-- The 64-bit product of two words. -/
def mulW (a b : Word) : BitVec 64 := a.setWidth 64 * b.setWidth 64

/-- What `umull` (`umull2` if `hi`) leaves. -/
def prodV (hi : Bool) (x m : BitVec 128) : BitVec 128 :=
  ofVDwords (mulW (vword x ((if hi then 2 else 0) + 0)) (vword m ((if hi then 2 else 0) + 0)))
    (mulW (vword x ((if hi then 2 else 0) + 1)) (vword m ((if hi then 2 else 0) + 1)))

theorem exec_umull (s : State) (hi : Bool) (d n m : VReg) :
    exec (.vop (.umull hi d n m)) s = some (s.setV d (prodV hi (s.v n) (s.v m))) := rfl

theorem exec_vorr (s : State) (d n m : VReg) :
    exec (.vop (.logic .orr d n m)) s = some (s.setV d (s.v n ||| s.v m)) := rfl

theorem prodF_words (x m : BitVec 128) {e : Nat} (he : e < 2) :
    vword (prodV false x m) (2 * e) = (mulW (vword x e) (vword m e)).extractLsb' 0 32 ∧
      vword (prodV false x m) (2 * e + 1) = (mulW (vword x e) (vword m e)).extractLsb' 32 32 := by
  rcases (by omega_using [he] : e = 0 ∨ e = 1) with rfl | rfl <;>
    exact ⟨by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl, by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl⟩

theorem prodT_words (x m : BitVec 128) {e : Nat} (he : e < 2) :
    vword (prodV true x m) (2 * e) = (mulW (vword x (2 + e)) (vword m (2 + e))).extractLsb' 0 32 ∧
      vword (prodV true x m) (2 * e + 1) = (mulW (vword x (2 + e)) (vword m (2 + e))).extractLsb' 32 32 := by
  rcases (by omega_using [he] : e = 0 ∨ e = 1) with rfl | rfl <;>
    exact ⟨by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl, by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl⟩

/-- What `rotl` leaves of the words `x`, for the multiplier `m`. -/
def rotV (x m : BitVec 128) : BitVec 128 :=
  VPermOp.eval .uzp1 .s4 (prodV false x m) (prodV true x m) |||
    VPermOp.eval .uzp2 .s4 (prodV false x m) (prodV true x m)

theorem vword_rotV (x m : BitVec 128) {r : Nat} (hr : r < 32)
    (hm : ∀ l < 4, vword m l = (1 : Word).rotateLeft r) {l : Nat} (hl : l < 4) :
    vword (rotV x m) l = (vword x l).rotateLeft r := by
  rw [rotV, vword_or, vword_uzp1 _ _ hl, vword_uzp2 _ _ hl]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by decide), ite_eq_left (by decide), (prodF_words x m (show 0 < 2 by decide)).1,
      (prodF_words x m (show 0 < 2 by decide)).2, hm 0 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_left (by decide), ite_eq_left (by decide), (prodF_words x m (show 1 < 2 by decide)).1,
      (prodF_words x m (show 1 < 2 by decide)).2, hm 1 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    show vword (prodV true x m) (2 * 0) ||| vword (prodV true x m) (2 * 0 + 1) = _
    rw [(prodT_words x m (show 0 < 2 by decide)).1, (prodT_words x m (show 0 < 2 by decide)).2, hm 2 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    show vword (prodV true x m) (2 * 1) ||| vword (prodV true x m) (2 * 1 + 1) = _
    rw [(prodT_words x m (show 1 < 2 by decide)).1, (prodT_words x m (show 1 < 2 by decide)).2, hm 3 (by decide)]
    exact rot_mul _ hr

theorem fReg_ne_tmp : ∀ k < 4, fReg k ≠ .v0 ∧ fReg k ≠ .v1 ∧ fReg k ≠ .v20 ∧ fReg k ≠ .v21 ∧ fReg k ≠ mulReg := by
  decide

theorem rotl_run (s : State) {k : Nat} (hk : k < 4) :
    ∃ s', runBlock isa (rotl k) s = some s' ∧ s'.v (fReg k) = rotV (s.v (fReg k)) (s.v mulReg) ∧
      VOnly [.v0, .v1, .v20, .v21, fReg k] s s' := by
  obtain ne := fReg_ne_tmp k hk
  let s₁ := s.setV .v0 (prodV false (s.v (fReg k)) (s.v mulReg))
  let s₂ := s₁.setV .v1 (prodV true (s₁.v (fReg k)) (s₁.v mulReg))
  let s₃ := s₂.setV (outReg 0) (VPermOp.eval .uzp1 .s4 (s₂.v .v0) (s₂.v .v1))
  let s₄ := s₃.setV (outReg 1) (VPermOp.eval .uzp2 .s4 (s₃.v .v0) (s₃.v .v1))
  let s₅ := s₄.setV (fReg k) (s₄.v (outReg 0) ||| s₄.v (outReg 1))
  obtain a1 : s₁.v (fReg k) = s.v (fReg k) := v_setV_of_ne _ _ ne.1
  obtain m1 : s₁.v mulReg = s.v mulReg := v_setV_of_ne _ _ (by decide)
  obtain z2 : s₂.v .v0 = prodV false (s.v (fReg k)) (s.v mulReg) :=
    (v_setV_of_ne _ _ (by decide)).trans (v_setV_self _ _ _)
  obtain o2 : s₂.v .v1 = prodV true (s.v (fReg k)) (s.v mulReg) := by
    show (s₁.setV _ _).v _ = _
    rw [v_setV_self, a1, m1]
  obtain z3 : s₃.v .v0 = s₂.v .v0 := v_setV_of_ne _ _ (by decide)
  obtain o3 : s₃.v .v1 = s₂.v .v1 := v_setV_of_ne _ _ (by decide)
  obtain p3 : s₃.v (outReg 0) = VPermOp.eval .uzp1 .s4 (s₂.v .v0) (s₂.v .v1) := v_setV_self _ _ _
  obtain p4 : s₄.v (outReg 0) = s₃.v (outReg 0) := v_setV_of_ne _ _ (by decide)
  obtain q4 : s₄.v (outReg 1) = VPermOp.eval .uzp2 .s4 (s₃.v .v0) (s₃.v .v1) := v_setV_self _ _ _
  refine ⟨s₅, ?_, ?_, ?_⟩
  · rw [rotl, runBlock_cons, exec_umull, runStep_some, runBlock_cons, exec_umull, runStep_some, runBlock_cons,
      exec_vperm, runStep_some, runBlock_cons, exec_vperm, runStep_some, runBlock_cons, exec_vorr, runStep_some,
      runBlock_nil]
  · show (s₄.setV _ _).v _ = _
    rw [v_setV_self, p4, q4, p3, z3, o3, z2, o2, rotV]
  · exact ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp [outReg]) _)).trans (VOnly.setV _ (by simp [outReg]) _)).trans (VOnly.setV _ (by simp) _)

/-- The registers the rotations write. -/
def rotRegs : List VReg := [.v0, .v1, .v20, .v21, .v12, .v13, .v14, .v15]

theorem rot_sub : ∀ k < 4, ∀ r ∈ [VReg.v0, .v1, .v20, .v21, fReg k], r ∈ rotRegs := by decide
theorem rot_other : ∀ k < 4, ∀ k' < 4, k ≠ k' → fReg k ∉ [VReg.v0, .v1, .v20, .v21, fReg k'] := by decide
theorem mul_notin : ∀ k < 4, mulReg ∉ [VReg.v0, .v1, .v20, .v21, fReg k] := by decide

theorem rotls_eq : (List.range 4).flatMap rotl = rotl 0 ++ (rotl 1 ++ (rotl 2 ++ (rotl 3 ++ []))) := rfl

theorem rotls_run (s : State) :
    ∃ s', runBlock isa ((List.range 4).flatMap rotl) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = rotV (s.v (fReg k)) (s.v mulReg)) ∧ VOnly rotRegs s s' := by
  obtain ⟨s₀, r₀, v₀, o₀⟩ := rotl_run s (show 0 < 4 by decide)
  obtain ⟨s₁, r₁, v₁, o₁⟩ := rotl_run s₀ (show 1 < 4 by decide)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := rotl_run s₁ (show 2 < 4 by decide)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := rotl_run s₂ (show 3 < 4 by decide)
  refine ⟨s₃, ?_, ?_, (((vmono o₀ (rot_sub 0 (by decide))).trans (vmono o₁ (rot_sub 1 (by decide)))).trans
    (vmono o₂ (rot_sub 2 (by decide)))).trans (vmono o₃ (rot_sub 3 (by decide)))⟩
  · rw [rotls_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · have ro := rot_other
    have mn := mul_notin
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [o₃.2 _ (ro 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (ro 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (ro 0 (by decide) 1 (by decide) (by decide)), v₀]
    · rw [o₃.2 _ (ro 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (ro 1 (by decide) 2 (by decide) (by decide)),
        v₁, o₀.2 _ (ro 1 (by decide) 0 (by decide) (by decide)), o₀.2 _ (mn 0 (by decide))]
    · rw [o₃.2 _ (ro 2 (by decide) 3 (by decide) (by decide)), v₂,
        o₁.2 _ (ro 2 (by decide) 1 (by decide) (by decide)), o₀.2 _ (ro 2 (by decide) 0 (by decide) (by decide)),
        o₁.2 _ (mn 1 (by decide)), o₀.2 _ (mn 0 (by decide))]
    · rw [v₃, o₂.2 _ (ro 3 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (ro 3 (by decide) 1 (by decide) (by decide)), o₀.2 _ (ro 3 (by decide) 0 (by decide) (by decide)),
        o₂.2 _ (mn 2 (by decide)), o₁.2 _ (mn 1 (by decide)), o₀.2 _ (mn 0 (by decide))]

/-! ## The mask and the halves -/

theorem v0_ne_fReg : ∀ k < 4, VReg.v0 ≠ fReg k := by decide
theorem bReg_ne_fReg : ∀ k < 4, ∀ k' < 4, bReg k ≠ fReg k' := by decide
theorem aReg_ne_fReg : ∀ k < 4, ∀ k' < 4, aReg k ≠ fReg k' := by decide
theorem aReg_ne_bReg : ∀ k < 4, ∀ k' < 4, aReg k ≠ bReg k' := by decide
theorem aReg_inj : ∀ k < 4, ∀ k' < 4, k ≠ k' → aReg k ≠ aReg k' := by decide
theorem bReg_inj : ∀ k < 4, ∀ k' < 4, k ≠ k' → bReg k ≠ bReg k' := by decide

/-- `I = Kmᵢ op R`, `Kmᵢ` in every lane of `v0`. -/
theorem mask_run (s : State) (o : Op) :
    ∃ s', runBlock isa ((List.range 4).map fun k => o.instr (fReg k) .v0 (bReg k)) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = opV o (s.v .v0) (s.v (bReg k))) ∧ VOnly fRegs s s' := by
  refine map4_run s (fun k => o.instr (fReg k) .v0 (bReg k)) fReg (fun k v => opV o (v .v0) (v (bReg k)))
    (fun k _ u => exec_op _ _ _ _ _) fReg_ne (fun k hk v v' h => ?_)
  show opV o (v' .v0) (v' (bReg k)) = opV o (v .v0) (v (bReg k))
  rw [h .v0 fun k' hk' _ => v0_ne_fReg k' hk', h (bReg k) fun k' hk' _ => bReg_ne_fReg k hk k' hk']

theorem feistel_eq : feistel = ((List.range 4).map fun k => veor (fReg k) (aReg k) (fReg k)) ++
    ((List.range 4).map fun k => .vop (.mov (aReg k) (bReg k))) ++
    ((List.range 4).map fun k => .vop (.mov (bReg k) (fReg k))) := rfl

/-- `(L, R) := (R, L ^ f)`. -/
theorem feistel_run (s : State) :
    ∃ s', runBlock isa feistel s = some s' ∧ (∀ k < 4, s'.v (aReg k) = s.v (bReg k)) ∧
      (∀ k < 4, s'.v (bReg k) = s.v (aReg k) ^^^ s.v (fReg k)) ∧ VOnly (fRegs ++ halfRegs) s s' := by
  obtain ⟨s₁, r₁, v₁, o₁⟩ := map4_run s (fun k => veor (fReg k) (aReg k) (fReg k)) fReg
    (fun k v => v (aReg k) ^^^ v (fReg k)) (fun k _ u => rfl) fReg_ne (fun k hk v v' h => by
      show v' (aReg k) ^^^ v' (fReg k) = v (aReg k) ^^^ v (fReg k)
      rw [h (aReg k) fun k' hk' _ => aReg_ne_fReg k hk k' hk',
        h (fReg k) fun k' hk' hne => fReg_ne k hk k' hk' (Ne.symm hne)])
  obtain ⟨s₂, r₂, v₂, o₂⟩ := map4_run s₁ (fun k => .vop (.mov (aReg k) (bReg k))) aReg
    (fun k v => v (bReg k)) (fun k _ u => rfl) aReg_inj (fun k hk v v' h => by
      show v' (bReg k) = v (bReg k)
      exact h (bReg k) fun k' hk' _ => (aReg_ne_bReg k' hk' k hk).symm)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := map4_run s₂ (fun k => .vop (.mov (bReg k) (fReg k))) bReg
    (fun k v => v (fReg k)) (fun k _ u => rfl) bReg_inj (fun k hk v v' h => by
      show v' (fReg k) = v (fReg k)
      exact h (fReg k) fun k' hk' _ => (bReg_ne_fReg k' hk' k hk).symm)
  obtain b₁ : ∀ k < 4, s₁.v (bReg k) = s.v (bReg k) := fun k hk => o₁.2 _ (by
    have := bReg_ne_fReg k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide)⟩)
  obtain f₂ : ∀ k < 4, s₂.v (fReg k) = s₁.v (fReg k) := fun k hk => o₂.2 _ (by
    have := aReg_ne_fReg; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(this 0 (by decide) k hk).symm, (this 1 (by decide) k hk).symm, (this 2 (by decide) k hk).symm,
      (this 3 (by decide) k hk).symm⟩)
  obtain a₃ : ∀ k < 4, s₃.v (aReg k) = s₂.v (aReg k) := fun k hk => o₃.2 _ (by
    have := aReg_ne_bReg k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide)⟩)
  refine ⟨s₃, ?_, fun k hk => ?_, fun k hk => ?_, ((vmono o₁ (by decide)).trans (vmono o₂ (by decide))).trans
    (vmono o₃ (by decide))⟩
  · rw [feistel_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃
  · rw [a₃ k hk, v₂ k hk, b₁ k hk]
  · rw [v₃ k hk, f₂ k hk, v₁ k hk]

/-! ## The subkeys -/

open VG.Impl.Cast5.AArch64 (rotate)
open VG.Proof.Cast5.AArch64 (rotate_ok)
open VG.Proof.Blowfish.AArch64 (exec_dup4)

theorem WP.exec_frame {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.syms = s.syms ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.syms he, Exec.sp he⟩

theorem low32 (x : Word) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem vword_dup (w : Word) {l : Nat} (hl : l < 4) : vword (ofVWords w w w w) l = w := by
  rw [vword_ofVWords _ _ _ _ hl]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The registers `subkeys` writes. -/
def subRegs : List Reg := [.x4, .x6, .x13, .x14, .x15]

/-- The others. -/
def keptRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x5, .x7, .x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24,
   .x25, .x26, .x27, .x28, .x30]

theorem kept_of_notin : ∀ r : Reg, r ∉ subRegs → r ∈ keptRegs := by
  intro r; cases r <;> decide

theorem subkeys_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 4)
    (h64 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 64) 4) :
    WP isa (.block subkeys) s fun u =>
      (∀ l < 4, vword (u.v .v0) l = s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32) ∧
      (∀ l < 4, vword (u.v mulReg) l =
        (1 : Word).rotateLeft ((s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32).toNat % 32)) ∧
      RFrame subRegs [.v0, mulReg] s u := by
  let km := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32
  let kr := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32
  let s₁ := s.write .w .x6 km
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  let s₃ := s₂.write .w .x13 kr
  let s₄ := s₃.write .w .x4 ((1 : BitVec 16).setWidth 32)
  have h64' : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x5 + BitVec.ofNat 64 64) 4 := h64
  obtain e₃ : exec (.ldr .w .x13 .x5 64) s₂ = some s₃ := exec_ldr_w (by decide) h64'
  rw [subkeys, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, by
    rw [runBlock_cons, exec_ldr_w (by decide) h0, runStep_some, runBlock_cons, exec_dup4, runStep_some,
      runBlock_cons, e₃, runStep_some, runBlock_cons, exec_movz_w, runStep_some, runBlock_nil], ?_⟩
  obtain hax : s₄.gpr .x4 = (1 : Word).setWidth 64 := gpr_write_self _ _ _ _
  obtain h13 : s₄.gpr .x13 = kr.setWidth 64 :=
    (gpr_write_of_ne _ _ _ (by decide)).trans (gpr_write_self _ _ _ _)
  refine WP.mono (WP.gprs (WP.exec_frame (rotate_ok s₄ hax h13)) (rs := keptRegs) (by decide) (by decide)) ?_
  rintro u ⟨⟨⟨hx4, hmem, hrd, hwr, hv⟩, hsy, hsp⟩, hg⟩
  let u' := u.setV mulReg (let w := (u.gpr .x4).setWidth 32; ofVWords w w w w)
  refine WP.of_runBlock ⟨u', by rw [runBlock_cons, exec_dup4, runStep_some, runBlock_nil], ?_, ?_, ?_⟩
  · intro l hl
    show vword ((u.setV _ _).v .v0) l = km
    rw [v_setV_of_ne _ _ (by decide), hv]
    show vword (ofVWords _ _ _ _) l = km
    rw [vword_dup _ hl]
    show ((s.write .w .x6 km).gpr .x6).setWidth 32 = km
    rw [gpr_write_self]
    exact low32 km
  · intro l hl
    show vword ((u.setV _ _).v mulReg) l = _
    rw [v_setV_self]
    show vword (ofVWords _ _ _ _) l = _
    rw [vword_dup _ hl, hx4]
    exact low32 _
  · refine ⟨fun r hr => ?_, fun r hr => ?_, hmem, hrd, hwr, hsp, hsy⟩
    · simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show u.gpr r = s.gpr r
      rw [hg r (kept_of_notin r (by simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr))]
      show (s₃.write .w .x4 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.1]
      show (s₂.write .w .x13 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.2.1]
      show (s.write .w .x6 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show (u.setV _ _).v r = s.v r
      rw [v_setV_of_ne _ _ hr.2, hv]
      exact v_setV_of_ne _ _ hr.1

/-! ## The round -/

/-- The vector registers a round writes before the halves trade places. -/
def preRegs : List VReg := rotRegs ++ planesRegs ++ stepRegs

/-- The vector registers a round writes. -/
def roundV : List VReg := .v27 :: preRegs ++ halfRegs

/-- The general-purpose registers a round writes. -/
def roundG : List Reg := [.x4, .x5, .x6, .x13, .x14, .x15]

theorem half_notin_pre : ∀ k < 4, aReg k ∉ preRegs ∧ bReg k ∉ preRegs ∧ aReg k ∉ [VReg.v0, mulReg] ∧
    bReg k ∉ [VReg.v0, mulReg] := by decide
theorem fReg_notin_planes : ∀ k < 4, fReg k ∉ planesRegs := by decide
theorem consts_notin : c64 ∉ preRegs ∧ c128 ∉ preRegs ∧ c64 ∉ [VReg.v0, mulReg] ∧ c128 ∉ [VReg.v0, mulReg] := by
  decide
theorem mul_notin_f : mulReg ∉ fRegs := by decide
theorem bReg_notin_f : ∀ k < 4, bReg k ∉ fRegs := by decide

theorem round_eq (t : Nat) (up : Bool) :
    round t up = subkeys ++ (((List.range 4).map fun k => (op t 0).instr (fReg k) .v0 (bReg k)) ++
      ((List.range 4).flatMap rotl ++ (planes fReg ++ (f t ++ (feistel ++
        [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4]))))) := by
  simp only [round, List.append_assoc]

/-- Round `i`, of Type `t`, on the sixteen blocks: `(L, R) := (R, L ^ f(R, Kmᵢ, Krᵢ))`, the
subkeys read at `x5` and `x5 + 64`. -/
theorem round_ok {s : State} {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hi : i % 3 = t % 3) (up : Bool)
    (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 4)
    (h64 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 64) 4) :
    WP isa (.block (round t up)) s fun s' =>
      (∀ n < 16, lane s'.v aReg n = lane s.v bReg n) ∧
      (∀ n < 16, lane s'.v bReg n = lane s.v aReg n ^^^
        Spec.Cast5.f i (lane s.v bReg n) (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32)
          (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32)) ∧
      s'.gpr .x5 = (if up then s.gpr .x5 + 4 else s.gpr .x5 - 4) ∧ RFrame roundG roundV s s' := by
  let km := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32
  let kr := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32
  obtain hr : kr.toNat % 32 < 32 := Nat.mod_lt _ (by decide)
  let I (n : Nat) : Word := (opEval (op t 0) km (lane s.v bReg n)).rotateLeft (kr.toNat % 32)
  rw [round_eq, WP.block_append_iff]
  refine WP.mono (subkeys_ok h0 h64) ?_
  rintro u ⟨hv0, hmul, fr⟩
  have hp := half_notin_pre
  obtain ⟨s₁, r₁, v₁, o₁⟩ := mask_run u (op t 0)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := rotls_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := planes_run s₂ fReg fReg_notin_planes
  obtain o₁₂ : VOnly preRegs u s₂ := (vmono o₁ (by decide)).trans (vmono o₂ (by decide))
  obtain o₁₃ : VOnly preRegs u s₃ := o₁₂.trans (vmono o₃ (by decide))
  obtain I₂ : ∀ n < 16, lane s₂.v fReg n = I n := by
    intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain hl : n % 4 < 4 := by omega_using []
    obtain hm₁ : ∀ l < 4, vword (s₁.v mulReg) l = (1 : Word).rotateLeft (kr.toNat % 32) := fun l hl => by
      rw [o₁.2 _ mul_notin_f]; exact hmul l hl
    simp only [lane]
    rw [v₂ _ hk, vword_rotV _ _ hr hm₁ hl, v₁ _ hk, vword_opV _ _ _ hl, hv0 _ hl, fr.v _ (hp _ hk).2.2.2]
    rfl
  obtain hx : ∀ j < 4, ∀ n < 16, vbyte (s₃.v (idxReg j)) n = Spec.Cast5.byte (I n) j := by
    intro j hj n hn
    rw [v₃ j hj n hn, vbyte_word _ (by omega_using [hj]), byte_eq, ← I₂ n hn]
    rfl
  obtain h9₃ : s₃.gpr .x9 = s₃.syms planesSym := by
    rw [o₁₃.gpr, o₁₃.1, fr.g _ (by decide)]
    show _ = u.syms planesSym
    rw [fr.syms]; exact h9
  obtain hc₃ : Consts s₃ :=
    ⟨fun e he => by rw [o₁₃.2 _ consts_notin.1, fr.v _ consts_notin.2.2.1]; exact hc.1 e he,
      fun e he => by rw [o₁₃.2 _ consts_notin.2.1, fr.v _ consts_notin.2.2.2]; exact hc.2 e he⟩
  obtain ⟨s₄, r₄, v₄, o₄⟩ := f_run h9₃ hc₃ t I hx
  obtain o₁₄ : VOnly preRegs u s₄ := o₁₃.trans (vmono o₄ (by decide))
  obtain ⟨s₅, r₅, va, vb, o₅⟩ := feistel_run s₄
  obtain o₁₅ : VOnly (preRegs ++ halfRegs) u s₅ := (vmono o₁₄ (by decide)).trans (vmono o₅ (by decide))
  let s₆ := s₅.write .x .x5 (if up then s₅.read .x .x5 + BitVec.ofNat _ 4 else s₅.read .x .x5 - BitVec.ofNat _ 4)
  obtain r₆ : runBlock isa [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] s₅ = some s₆ := by
    cases up
    · rw [runBlock_cons]; simp only [Bool.false_eq_true, ite_false]
      rw [exec_subImm_x (by decide), runStep_some, runBlock_nil]; rfl
    · rw [runBlock_cons]; simp only [ite_true]
      rw [exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
  obtain cat := @VG.AArch64.Tbl.runBlock_cat_some
  refine WP.of_runBlock ⟨s₆, cat r₁ (cat r₂ (cat r₃ (cat r₄ (cat r₅ r₆)))), ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    simp only [lane]
    show vword (s₅.v _) _ = _
    rw [va _ hk, o₁₄.2 _ (hp _ hk).2.1, fr.v _ (hp _ hk).2.2.2]
  · intro n hn
    obtain hk : n / 4 < 4 := by omega_using [hn]
    obtain hf := v₄ n hn
    simp only [lane] at hf ⊢
    show vword (s₅.v _) _ = _
    rw [vb _ hk, Proof.Blowfish.AArch64.vword_xor, hf, o₁₄.2 _ (hp _ hk).1, fr.v _ (hp _ hk).2.2.1,
      f_eq_fAcc ht hi]
    rfl
  · show (s₅.write .x .x5 _).gpr .x5 = _
    rw [gpr_write_self]
    simp only [State.read, BitVec.setWidth_eq]
    rw [o₁₅.gpr, fr.g _ (by decide)]
    cases up <;> rfl
  · refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [roundG, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show (s₅.write .x .x5 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.1, o₁₅.gpr, fr.g _ (by
        simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩)]
    · have h27 : r ≠ .v27 := fun h => hr (h ▸ List.mem_cons_self)
      obtain hrest : r ∉ preRegs ++ halfRegs := fun h => hr (List.mem_cons_of_mem _ h)
      show s₅.v r = _
      rw [o₁₅.2 _ hrest, fr.v _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hrest (by subst h; decide), h27⟩)]
    · show s₅.mem = _
      rw [o₁₅.mem, fr.mem]
    · show s₅.rd = _
      rw [o₁₅.rd, fr.rd]
    · show s₅.wr = _
      rw [o₁₅.wr, fr.wr]
    · show s₅.sp = _
      rw [o₁₅.1, fr.sp]
    · show s₅.syms = _
      rw [o₁₅.1, fr.syms]

end VG.Proof.Cast5.AArch64.Tbl

/-!
## CAST5 on AArch64: the rounds on sixteen blocks

`cipherEnc_ok`, `cipherDec_ok`: `cipher up`, with the subkeys at `x0` and
their number, 12 or 16, in `x16`, leaves in `A` and `B` the halves of each of
the sixteen blocks after its rounds (`encFold`, `decFold`).
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg c64 c128)
open VG.Spec.Cast5 (Word Schedule)
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ add_ofNat_add)
open VG.Proof.Cast5.AArch64 (wp_countdown groups_x7 x8_zero dec_x12 four decFold_zero)
open VG.Proof.Blowfish.AArch64 (lane Consts)
open VG.Proof.MlKem.AArch64 (eval_zero)

/-- What the rounds read: the table's address in `x9`, the constants of the
lookups, and the subkeys `k` at `x0`. -/
structure CPre (s : State) (k : Schedule) : Prop where
  x9 : s.gpr .x9 = s.syms planesSym
  consts : Consts s
  sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0

/-- The general-purpose registers the rounds write. -/
def cipherG : List Reg := [.x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15]

/-- The halves of the sixteen blocks, in `A` and `B`. -/
def Halves (v : VReg → BitVec 128) (lr : Nat → Word × Word) : Prop :=
  ∀ n < 16, (lane v aReg n, lane v bReg n) = lr n

theorem consts_notin_round : c64 ∉ roundV ∧ c128 ∉ roundV := by decide

theorem round_step {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {t i : Nat}
    (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : i % 3 = t % 3) (hi : 1 ≤ i ∧ i ≤ 16)
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) {lr : Nat → Word × Word}
    (hl : Halves u.v lr) :
    WP isa (.block (round t up)) u fun v =>
      Halves v.v (fun n => Spec.Cast5.round k i (lr n)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = (if up then u.gpr .x5 + 4 else u.gpr .x5 - 4) ∧ v.gpr .x7 = u.gpr .x7 ∧
      v.gpr .x8 = u.gpr .x8 := by
  obtain x0 : u.gpr .x0 = s.gpr .x0 := fr.g _ (by decide)
  obtain h9 : u.gpr .x9 = u.syms planesSym := by rw [fr.g _ (by decide), fr.syms]; exact P.x9
  obtain hc : Consts u :=
    ⟨fun e he => by rw [fr.v _ consts_notin_round.1]; exact P.consts.1 e he,
      fun e he => by rw [fr.v _ consts_notin_round.2]; exact P.consts.2 e he⟩
  obtain sched : InRegions (u.rd ++ u.wr) (u.gpr .x0) 128 := by rw [fr.rd, fr.wr, x0]; exact P.sched
  obtain e0 : u.gpr .x5 + BitVec.ofNat 64 0 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [h5, add_ofNat_add]; rfl
  obtain e64 : u.gpr .x5 + BitVec.ofNat 64 64 = u.gpr .x0 + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h5, add_ofNat_add]; congr 2; omega_using [hi]
  obtain h0 : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 0) 4 := by
    rw [e0]; exact CallLay.inRegions_sub sched (by omega_using [hi]) (by decide)
  obtain h64 : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 64) 4 := by
    rw [e64]; exact CallLay.inRegions_sub sched (by omega_using [hi]) (by decide)
  refine WP.mono (round_ok ht hti up h9 hc h0 h64) ?_
  rintro v ⟨va, vb, v5, vf⟩
  refine ⟨fun n hn => ?_, fr.trans (vf.mono (by decide) (fun _ h => h)), v5, vf.g _ (by decide),
    vf.g _ (by decide)⟩
  show _ = Spec.Cast5.round k i (lr n)
  rw [va n hn, vb n hn, e0, e64, x0, fr.mem, P.key _ (by omega_using [hi]), P.key _ (by omega_using [hi]),
    ← hl n hn]
  rfl

theorem countDown_ok {s u : State} (fr : RFrame cipherG roundV s u) {lr : Nat → Word × Word}
    (hl : Halves u.v lr) :
    WP isa (.block [.subImm .x .x7 .x7 1]) u fun v => Halves v.v lr ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = u.gpr .x5 ∧ v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  refine WP.of_runBlock ⟨u.write .x .x7 (u.read .x .x7 - BitVec.ofNat _ 1), by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], hl, ?_,
    gpr_write_of_ne _ _ _ (by decide), gpr_write_self _ _ _ _, gpr_write_of_ne _ _ _ (by decide)⟩
  refine fr.trans ⟨fun r hr => gpr_write_of_ne _ _ _ fun e => hr (by rw [e]; decide), fun _ _ => rfl, rfl, rfl,
    rfl, rfl, rfl⟩

theorem groupEnc_eq : group true = round 1 true ++ (round 2 true ++ (round 3 true ++
    ([.subImm .x .x7 .x7 1] : List Instr))) := by
  simp only [group, ite_true, List.append_assoc]

theorem groupDec_eq : group false = round 3 false ++ (round 2 false ++ (round 1 false ++
    ([.subImm .x .x7 .x7 1] : List Instr))) := by
  simp only [group, Bool.false_eq_true, ite_false, List.append_assoc]

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {g : Nat}
    (hg : 3 * g + 3 ≤ 16) {lr : Nat → Word × Word} (hl : Halves u.v (fun n => encFold k (3 * g) (lr n)))
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (12 * g)) :
    WP isa (.block (group true)) u fun v =>
      Halves v.v (fun n => encFold k (3 * (g + 1)) (lr n)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (12 * (g + 1)) ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  obtain hdi : ∀ {v : State}, RFrame cipherG roundV s v → v.gpr .x0 = u.gpr .x0 :=
    fun hv => (hv.g .x0 (by decide)).trans (fr.g .x0 (by decide)).symm
  rw [groupEnc_eq, WP.block_append_iff]
  refine WP.mono (round_step P fr (t := 1) (i := 3 * g + 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [h5]; congr 2; omega_arith) true hl) fun v₁ ⟨l₁, f₁, a₁, b₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_left rfl, h5, hdi f₁, four, add_ofNat_add]; congr 2; omega_arith) true l₁)
    fun v₂ ⟨l₂, f₂, a₂, b₂, c₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h5, hdi f₂, four, add_ofNat_add, add_ofNat_add]
        congr 2; omega_arith) true l₂) fun v₃ ⟨l₃, f₃, a₃, b₃, c₃⟩ => ?_
  refine WP.mono (countDown_ok f₃ l₃) fun v₄ ⟨l₄, f₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨fun n hn => ?_, f₄, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · show _ = encFold k (3 * (g + 1)) (lr n)
    rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega_arith, encFold_succ, encFold_succ, encFold_succ]
    exact l₄ n hn
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h5, hdi f₄, four,
      add_ofNat_add, add_ofNat_add, add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega_arith]

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {n m : Nat}
    (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0) {lr : Nat → Word × Word}
    (hl : Halves u.v (fun j => decFold k n m (lr j)))
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - m - 1))) :
    WP isa (.block (group false)) u fun v =>
      Halves v.v (fun j => decFold k n (m + 3) (lr j)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = u.gpr .x5 - 12 ∧ v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  obtain hdi : ∀ {v : State}, RFrame cipherG roundV s v → v.gpr .x0 = u.gpr .x0 :=
    fun hv => (hv.g .x0 (by decide)).trans (fr.g .x0 (by decide)).symm
  have sub4 (x : Addr) (a : Nat) (ha : 4 ≤ a) :
      x + BitVec.ofNat 64 a - 4 = x + BitVec.ofNat 64 (a - 4) := by
    rw [show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_sub _ ha]
  rw [groupDec_eq, WP.block_append_iff]
  refine WP.mono (round_step P fr (t := 3) (i := n - m) (by decide) (by omega_arith) (by omega_arith)
    h5 false hl) fun v₁ ⟨l₁, f₁, a₁, b₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₁ (t := 2) (i := n - m - 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_right Bool.false_ne_true, h5, hdi f₁, sub4 _ _ (by omega_arith)]; congr 2; omega_arith)
    false l₁) fun v₂ ⟨l₂, f₂, a₂, b₂, c₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₂ (t := 1) (i := n - m - 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_right Bool.false_ne_true, a₁, ite_eq_right Bool.false_ne_true, h5, hdi f₂,
      sub4 _ _ (by omega_arith), sub4 _ _ (by omega_arith)]; congr 2; omega_arith) false l₂)
    fun v₃ ⟨l₃, f₃, a₃, b₃, c₃⟩ => ?_
  refine WP.mono (countDown_ok f₃ l₃) fun v₄ ⟨l₄, f₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨fun j hj => ?_, f₄, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · show _ = decFold k n (m + 3) (lr j)
    rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega_arith,
      show n - (m + 2) = n - m - 2 by omega_arith]
    exact l₄ j hj
  · rw [a₄, a₃, a₂, a₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl

/-! ## The rounds -/

theorem cipherEnc_eq : cipher true =
    .seq (.block (([.addImm .x .x5 .x0 0] : List Instr) ++ groups))
      (.seq (.loop (.block (group true)) (.nonzero .x .x7))
        (.ite (.zero .x .x8) (.block (round 1 true)) (.block []))) := rfl

theorem cipherDec_eq : cipher false =
    .seq (.block (([.lsl .x .x5 .x16 2, .add .x .x5 .x5 .x0, .subImm .x .x5 .x5 4] : List Instr) ++ groups))
      (.seq (.ite (.zero .x .x8) (.block (round 1 false)) (.block []))
        (.loop (.block (group false)) (.nonzero .x .x7))) := rfl

theorem RFrame.refl (gs : List Reg) (vs : List VReg) (s : State) : RFrame gs vs s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RFrame.write {gs : List Reg} {vs : List VReg} {s u : State} (h : RFrame gs vs s u) {d : Reg}
    (hd : d ∈ gs) (a : BitVec 64) : RFrame gs vs s (u.write .x d a) :=
  h.trans ⟨fun r hr => gpr_write_of_ne _ _ _ fun e => hr (by rw [e]; exact hd), fun _ _ => rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Encryption's rounds, 12 or 16, on the sixteen blocks. -/
theorem cipherEnc_ok {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher true) s fun v =>
      Halves v.v (fun m => encFold k n (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  obtain hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 := by rcases hn with rfl | rfl <;> decide
  let lr (m : Nat) : Word × Word := (lane s.v aReg m, lane s.v bReg m)
  obtain start : WP isa (.block (([.addImm .x .x5 .x0 0] : List Instr) ++ groups)) s fun u =>
      Halves u.v lr ∧ RFrame cipherG roundV s u ∧ u.gpr .x5 = u.gpr .x0 ∧
      u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧ u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
    unfold groups
    crun [h16]
    exact ⟨fun m _ => rfl, ((((RFrame.refl _ _ s).write (by decide) _).write (by decide) _).write (by decide) _).write
      (by decide) _, BitVec.add_zero _, groups_x7 hn⟩
  rw [cipherEnc_eq]
  refine WP.seq (WP.mono start fun u ⟨hu, fu, u5, u7, u8⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2 hG.1
    (fun g v => Halves v.v (fun m => encFold k (3 * g) (lr m)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (12 * g) ∧ v.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16)
    (fun g hg v ⟨hv, fv, h5, h8⟩ _ =>
      WP.mono (groupEnc_ok P fv (by rcases hn with rfl | rfl <;> omega_arith) hv h5)
        fun w ⟨hw, fw, w5, w7, w8⟩ => ⟨⟨hw, fw, w5, w8.trans h8⟩, w7⟩)
    ⟨fun m hm => hu m hm, fu, by rw [u5, Nat.mul_zero, BitVec.add_zero], u8⟩ u7) fun v ⟨hv, fv, v5, v8⟩ => ?_)
  refine WP.ite (decide (n = 16)) (by rw [eval_zero, v8, x8_zero hn]) (fun hd => ?_) (fun hd => ?_)
  · have e : n = 16 := of_decide_eq_true hd
    subst e
    refine WP.mono (round_step P fv (t := 1) (i := 16) (by decide) (by decide) (by decide) v5 true hv)
      fun x ⟨hx, fx, _, _, _⟩ => ⟨fun m hm => ?_, fx⟩
    show _ = encFold k (15 + 1) (lr m)
    rw [encFold_succ]
    exact hx m hm
  · have e : n = 12 := by
      rcases hn with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false hd)
    subst e
    exact WP.block_nil ⟨fun m hm => hv m hm, fv⟩

/-- Decryption's rounds, 12 or 16, on the sixteen blocks. -/
theorem cipherDec_ok {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher false) s fun v =>
      Halves v.v (fun m => decFold k n n (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  obtain hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases hn with rfl | rfl <;> decide
  let lr (m : Nat) : Word × Word := (lane s.v aReg m, lane s.v bReg m)
  obtain start : WP isa (.block (([.lsl .x .x5 .x16 2, .add .x .x5 .x5 .x0, .subImm .x .x5 .x5 4] :
      List Instr) ++ groups)) s fun u =>
      Halves u.v lr ∧ RFrame cipherG roundV s u ∧ u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - 1)) ∧
      u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧ u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
    unfold groups
    crun [h16]
    exact ⟨fun m _ => rfl, ((((((RFrame.refl _ _ s).write (by decide) _).write (by decide) _).write (by decide) _).write
      (by decide) _).write (by decide) _).write (by decide) _, dec_x12 hn _, groups_x7 hn⟩
  rw [cipherDec_eq]
  refine WP.seq (WP.mono start fun u ⟨hu, fu, u5, u7, u8⟩ => ?_)
  obtain first : WP isa (.ite (.zero .x .x8) (.block (round 1 false)) (.block [])) u fun v =>
      Halves v.v (fun m => decFold k n (n % 3) (lr m)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (4 * (n - n % 3 - 1)) ∧
      v.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) (by rw [eval_zero, u8, x8_zero hn]) (fun hd => ?_) (fun hd => ?_)
    · have e : n = 16 := of_decide_eq_true hd
      subst e
      refine WP.mono (round_step P fu (t := 1) (i := 16) (by decide) (by decide) (by decide) u5 false hu)
        fun x ⟨hx, fx, x5, x7, _⟩ => ⟨fun m hm => ?_, fx, ?_, x7.trans u7⟩
      · show _ = decFold k 16 (0 + 1) (lr m)
        rw [decFold_succ, decFold_zero]
        exact hx m hm
      · have hdi : x.gpr .x0 = u.gpr .x0 := (fx.g .x0 (by decide)).trans (fu.g .x0 (by decide)).symm
        rw [x5, ite_eq_right Bool.false_ne_true, u5, hdi, four, Offset.add_ofNat_sub _ (by decide)]
    · have e : n = 12 := by
        rcases hn with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false hd)
      subst e
      exact WP.block_nil ⟨fun m hm => hu m hm, fu, u5, u7⟩
  refine WP.seq (WP.mono first fun v ⟨hv, fv, v5, v7⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => Halves w.v (fun m => decFold k n (n % 3 + 3 * g) (lr m)) ∧ RFrame cipherG roundV s w ∧
      (n % 3 + 3 * g < n → w.gpr .x5 = w.gpr .x0 + BitVec.ofNat 64 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, fw, w5⟩ _ => WP.mono (groupDec_ok P fw (m := n % 3 + 3 * g) (by omega_arith) (by
        rcases hn with rfl | rfl <;> decide) (by omega_arith) hw (w5 (by omega_arith)))
      fun x ⟨hx, fx, x5, x7, _⟩ => ⟨⟨fun m hm => ?_, fx, fun hlt => ?_⟩, x7⟩)
    ⟨fun m hm => hv m hm, fv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact v5⟩ v7)
    fun w ⟨hw, fw, _⟩ => ⟨fun m hm => ?_, fw⟩
  · show _ = decFold k n (n % 3 + 3 * (g + 1)) (lr m)
    rw [show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega_arith]
    exact hx m hm
  · have hdi : x.gpr .x0 = w.gpr .x0 := (fx.g .x0 (by decide)).trans (fw.g .x0 (by decide)).symm
    rw [x5, w5 (by omega_arith), hdi, show (12 : Addr) = BitVec.ofNat 64 12 from rfl,
      Offset.add_ofNat_sub _ (by omega_arith)]
    congr 2
    omega_arith
  · have := hw m hm
    rw [hG.2.2.1] at this
    exact this

end VG.Proof.Cast5.AArch64.Tbl

/-!
## CAST5 on AArch64: a batch of sixteen blocks

`batch_ok`: `batch up` replaces each of the sixteen blocks at `x4` with its
encryption (`up`) or decryption, with the subkeys at `x0` and their number in
`x16`. The loads and stores are Blowfish's (`loadBatch`, `storeBatch`,
`Proof/Blowfish/AArch64/Batch.lean`), whose blocks have the same encoding.
-/

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg c64 c128 loadBatch storeBatch)
open VG.Spec.Cast5 (Word Schedule Block)
open VG.Proof.Cast5 (encFold decFold)
open VG.Proof.Blowfish.AArch64 (lane Consts loadBatch_run storeBatch_run outByte cat_run halfRegs)
open VG.AArch64.Tbl (VOnly)

/-! ## The blocks' encoding -/

theorem cat4_byte (a b c d : BitVec 8) {j : Nat} (hj : j < 4) :
    (a ++ b ++ c ++ d : BitVec 32).extractLsb' (8 * j) 8 = [d, c, b, a].getD j 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simp [hi]
  · simp [hi, show ¬ 8 + i < 8 by omega]
  · simp [hi, show ¬ 16 + i < 8 by omega, show 16 + i - 8 = 8 + i by omega]
  · simp [hi, show ¬ 24 + i < 8 by omega, show 24 + i - 8 = 16 + i by omega, show 16 + i - 8 = 8 + i by omega,
      show ¬ 8 + i < 8 by omega, show ¬ 16 + i < 8 by omega]

/-- The halves of a block are Blowfish's big-endian words. -/
theorem decodeBlock_eq (b : Block) :
    Spec.Cast5.decodeBlock b = (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4) := by
  refine Prod.ext (Proof.Blowfish.word_ext fun j hj => ?_) (Proof.Blowfish.word_ext fun j hj => ?_)
  · rw [Proof.Blowfish.decodeWord_byte _ _ hj]
    show (b[0] ++ b[1] ++ b[2] ++ b[3] : BitVec 32).extractLsb' (8 * j) 8 = _
    rw [cat4_byte _ _ _ _ hj]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp [Vector.getD, Array.getD]
  · rw [Proof.Blowfish.decodeWord_byte _ _ hj]
    show (b[4] ++ b[5] ++ b[6] ++ b[7] : BitVec 32).extractLsb' (8 * j) 8 = _
    rw [cat4_byte _ _ _ _ hj]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      simp [Vector.getD, Array.getD]

theorem encodeBlock_eq (x y : Word) : Spec.Cast5.encodeBlock (x, y) = Spec.Blowfish.encodeBlock x y := by
  refine congrArg Vector.ofFn (funext fun i => ?_)
  have := i.isLt
  by_cases h : i.val < 4
  · simp only [h, ite_true, show i.val % 4 = i.val by omega]
  · simp only [h, ite_false, show 3 - i.val % 4 = 7 - i.val by omega]

/-! ## The batch -/

/-- The halves after the rounds of encryption (`up`) or decryption. -/
def foldOut (k : Schedule) (n : Nat) (up : Bool) (lr : Word × Word) : Word × Word :=
  if up then encFold k n lr else decFold k n n lr

/-- A block's encryption (`up`) or decryption. -/
def blockOut (k : Schedule) (n : Nat) (up : Bool) (b : Block) : Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

theorem blockOut_eq (k : Schedule) (n : Nat) (up : Bool) (b : Block) :
    blockOut k n up b =
      Spec.Blowfish.encodeBlock (foldOut k n up (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4)).2
        (foldOut k n up (Spec.Blowfish.decodeWord b 0, Spec.Blowfish.decodeWord b 4)).1 := by
  rw [← encodeBlock_eq, ← decodeBlock_eq]
  cases up <;> rfl

theorem cipher_ok (up : Bool) {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher up) s fun v =>
      Halves v.v (fun m => foldOut k n up (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  cases up
  · exact cipherDec_ok P hn h16
  · exact cipherEnc_ok P hn h16

/-- What the rounds read, in a state that keeps it. -/
theorem CPre.frame {s u : State} {k : Schedule} (P : CPre s k) {gs : List Reg} {vs : List VReg}
    (fr : RFrame gs vs s u) (h0 : Reg.x0 ∉ gs) (h9 : Reg.x9 ∉ gs) (hc : c64 ∉ vs ∧ c128 ∉ vs) : CPre u k :=
  ⟨by rw [fr.g _ h9, fr.syms]; exact P.x9,
    ⟨fun e he => by rw [fr.v _ hc.1]; exact P.consts.1 e he, fun e he => by rw [fr.v _ hc.2]; exact P.consts.2 e he⟩,
    by rw [fr.rd, fr.wr, fr.g _ h0]; exact P.sched, fun j hj => by rw [fr.mem, fr.g _ h0]; exact P.key j hj⟩

/-- The general-purpose registers a batch writes. -/
def batchG : List Reg := [.x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15, .x17]

structure BatchPost (k : Schedule) (n : Nat) (up : Bool) (s s' : State) : Prop where
  out : ∀ j < 16, Spec.Cast5.blockAt s'.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)) =
    blockOut k n up (Spec.Cast5.blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * j)))
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem
  x4 : s'.gpr .x4 = s.gpr .x4
  gpr : ∀ r, r ∉ batchG → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ roundV → s'.v r = s.v r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem io_sub : ∀ r ∈ (VReg.v20 :: .v21 :: halfRegs), r ∈ roundV := by decide
theorem consts_notin_io : c64 ∉ (VReg.v20 :: .v21 :: halfRegs) ∧ c128 ∉ (VReg.v20 :: .v21 :: halfRegs) := by decide

theorem batch_ok (up : Bool) {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n)
    (hW : ∀ j < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (batch up) s (BatchPost k n up s) := by
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadBatch_run (s := s) fun j hj => by
    obtain ⟨r, hr, hc'⟩ := hW j hj; exact ⟨r, List.mem_append_right _ hr, hc'⟩
  let s₂ := s₁.write .x .x17 (s₁.read .x .x4 + BitVec.ofNat _ 0)
  obtain fr₂ : RFrame batchG roundV s s₂ :=
    ((RFrame.ofV o₁).mono (fun _ h => absurd h List.not_mem_nil) io_sub).write (by decide) _
  obtain fr₂' : RFrame [.x17] (VReg.v20 :: .v21 :: halfRegs) s s₂ :=
    ((RFrame.ofV o₁).mono (fun _ h => absurd h List.not_mem_nil) (fun _ h => h)).write (by decide) _
  obtain x17₂ : s₂.gpr .x17 = s.gpr .x4 := by
    show (s₁.write .x .x17 _).gpr .x17 = _
    rw [gpr_write_self]
    show s₁.gpr .x4 + BitVec.ofNat 64 0 = _
    rw [o₁.gpr]; exact BitVec.add_zero _
  rw [batch]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, cat_run r₁ (by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]), ?_⟩
  obtain P₂ : CPre s₂ k := P.frame fr₂' (by decide) (by decide) consts_notin_io
  apply WP.seq
  refine WP.mono (cipher_ok up P₂ hn (by rw [fr₂.g _ (by decide)]; exact h16)) ?_
  rintro s₃ ⟨hl, fr₃⟩
  let s₄ := s₃.write .x .x4 (s₃.read .x .x17 + BitVec.ofNat _ 0)
  obtain x4₄ : s₄.gpr .x4 = s.gpr .x4 := by
    show (s₃.write .x .x4 _).gpr .x4 = _
    rw [gpr_write_self]
    show s₃.gpr .x17 + BitVec.ofNat 64 0 = _
    rw [fr₃.g _ (by decide), x17₂]; exact BitVec.add_zero _
  obtain fr₄ : RFrame batchG roundV s s₄ :=
    (fr₂.trans (fr₃.mono (by decide) (fun _ h => h))).write (by decide) _
  obtain hW₄ : ∀ j < 8, InRegions s₄.wr (s₄.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16 := fun j hj => by
    rw [fr₄.wr, x4₄]; exact hW j hj
  obtain ⟨s₅, r₅, m₅, f₅, o₅⟩ := storeBatch_run hW₄
  refine WP.of_runBlock ⟨s₅, cat_run (by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]) r₅, ?_⟩
  rw [x4₄] at m₅ f₅
  refine ⟨fun j hj => ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · refine Proof.Blowfish.blockAt_eq _ _ _ fun i hi => ?_
    obtain hj4 : j / 4 < 4 := by omega_using [hj]
    obtain hlj : (lane s₃.v aReg j, lane s₃.v bReg j) = foldOut k n up (lane s₂.v aReg j, lane s₂.v bReg j) :=
      hl j hj
    have ha : lane s₂.v aReg j = lane s₁.v aReg j := rfl
    have hb : lane s₂.v bReg j = lane s₁.v bReg j := rfl
    rw [ha, hb, a₁ j hj, b₁ j hj] at hlj
    have hA : lane s₄.v aReg j = lane s₃.v aReg j := rfl
    have hB : lane s₄.v bReg j = lane s₃.v bReg j := rfl
    rw [Offset.add_add, m₅ _ (by omega_using [hj, hi]), outByte, show (8 * j + i) / 8 = j by omega_using [hi],
      show (8 * j + i) % 8 = i by omega_using [hi], blockOut_eq, hA, hB]
    show _ = (Spec.Blowfish.encodeBlock (foldOut k n up _).2 (foldOut k n up _).1).getD i 0
    obtain e1 := congrArg Prod.fst hlj
    obtain e2 := congrArg Prod.snd hlj
    simp only at e1 e2
    rw [e1, e2]
    rfl
  · have m₄ : s₄.mem = s.mem := fr₄.mem
    rw [← m₄]; exact f₅
  · rw [o₅.gpr, x4₄]
  · rw [o₅.gpr, fr₄.g _ hr]
  · rw [o₅.v _ (fun h => hr (io_sub _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))), fr₄.v _ hr]
  · rw [o₅.rd, fr₄.rd]
  · rw [o₅.wr, fr₄.wr]
  · rw [o₅.sp, fr₄.sp]
  · rw [o₅.eq, fr₄.syms]

end VG.Proof.Cast5.AArch64.Tbl
