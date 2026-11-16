module

public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.Bytes

/-! # Triple DES key expansion on AArch64

`roundKey_bit`: bit `j` of round key `r` is the key bit `sel r (47 - j)`.
`spread_run`: `spread` leaves the table of a component key in `v16`–`v19`
(`Tab`). `pair_run`: `pairCode` stores the vector `pairVec` of two round keys,
whose bits are the table's at the static's indices, the round keys'
(`pairVec_dword`). `component_ok`: a component's sixteen round keys;
`componentStep_ok`, `copyThird_ok`, `Components.schedule`: the three
components are the schedule.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.Spec.TripleDes VG.Proof.TripleDes VG.Impl.TripleDes.AArch64.Key

/-- The rotation of the halves after `n` rounds. -/
def tot (n : Nat) : Nat := ((List.range n).map fun j => rotations.getD j 0).sum

theorem tot_step : ∀ n < 16, rotations.getD n 0 < 28 ∧ tot (n + 1) = tot n + rotations.getD n 0 ∧
    tot (n + 1) ≤ 28 := by decide

theorem rotate_bit (x : BitVec 28) (n : Nat) (hn : n < 28) (j : Nat) (hj : j < 28) :
    (x.rotateLeft n).getLsbD j = x.getLsbD ((j + 28 - n) % 28) := by
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn]
  by_cases h : j < n
  · simp only [h]
    exact congrArg x.getLsbD (by omega_using [h, hn])
  · simp only [h, hj, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega_using [h, hj])

theorem halves_bit (key : BitVec 64) : ∀ n ≤ 16, ∀ j < 28,
    (keyPrefix key n).1.getLsbD j = (keyInitial key).1.getLsbD ((j + 448 - tot n) % 28) ∧
    (keyPrefix key n).2.1.getLsbD j = (keyInitial key).2.1.getLsbD ((j + 448 - tot n) % 28) := by
  intro n
  induction n with
  | zero =>
    intro _ j hj
    have : (j + 448 - tot 0) % 28 = j := by
      rw [show tot 0 = 0 from rfl]; omega_using [hj]
    rw [this]; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro hn j hj
    have hs := tot_step n (by omega_using [hn])
    have hm : (j + 28 - rotations.getD n 0) % 28 < 28 := Nat.mod_lt _ (by decide)
    have ih' := ih (by omega_using [hn]) _ hm
    have idx : ((j + 28 - rotations.getD n 0) % 28 + 448 - tot n) % 28 =
        (j + 448 - tot (n + 1)) % 28 := by
      omega_using [hs.1, hs.2.1, hs.2.2, hj]
    rw [keyPrefix_succ]
    simp only [keyStep]
    rw [rotate_bit _ _ hs.1 _ hj, rotate_bit _ _ hs.1 _ hj, ih'.1, ih'.2, idx]
    exact ⟨rfl, rfl⟩

theorem stored (key : BitVec 64) : ∀ n ≤ 16, ∀ r < n,
    (keyPrefix key n).2.2.getD r 0 =
      permute pc2 ((keyPrefix key (r + 1)).1 ++ (keyPrefix key (r + 1)).2.1) := by
  intro n
  induction n with
  | zero => intro _ r hr; omega
  | succ n ih =>
    intro hn r hr
    rw [keyPrefix_succ]
    by_cases h : r = n
    · subst h
      rw [vector_getD _ _ (by omega_using [hn])]
      rw [keyPrefix_succ]
      simp only [keyStep, Vector.set!_eq_setIfInBounds, Vector.getElem_setIfInBounds_self]
    · have hlt : r < n := by omega_using [hr, h]
      rw [← ih (by omega_using [hn]) r hlt, vector_getD _ _ (by omega_using [hn, hr]),
        vector_getD _ _ (by omega_using [hn, hr])]
      simp only [keyStep, Vector.set!_eq_setIfInBounds]
      exact Vector.getElem_setIfInBounds_ne _ (fun e => h e.symm)

/-- The bit of `permute pc1 key` that is bit `j` of round key `r`. -/
def src (r j : Nat) : Nat :=
  let t := 56 - pc2.getD (47 - j) 1
  if t < 28 then (t + 448 - tot (r + 1)) % 28 else 28 + (t - 28 + 448 - tot (r + 1)) % 28

/-- `pc1.getD i 1`, with the index evaluated first. The kernel remembers the value of a term by
the term, so it then reads `pc1` once for each of its 56 entries, rather than once for every
bit of every round key, whose index is another term each time. -/
private def pc1At (i : Nat) : Nat :=
  Nat.casesOn (motive := fun _ => Nat) (Nat.succ i) (pc1.getD i 1) (fun m => pc1.getD m 1)

private theorem pc1At_eq (i : Nat) : pc1At i = pc1.getD i 1 := rfl

/-- `sel`, reading `pc1` with `pc1At`. -/
private def selAt (r i : Nat) : Nat :=
  let q := pc2.getD i 1
  let u := if q ≤ 28 then (q - 1 + shiftOf r) % 28 + 1 else (q - 29 + shiftOf r) % 28 + 29
  pc1At (u - 1)

private theorem selAt_eq (r i : Nat) : selAt r i = sel r i := rfl

theorem src_sel : ∀ r < 16, ∀ j < 48, src r j < 56 ∧
    64 - pc1.getD (55 - src r j) 1 = 64 - sel r (47 - j) ∧ 1 ≤ sel r (47 - j) ∧
    sel r (47 - j) ≤ 64 ∧ 1 ≤ pc2.getD (47 - j) 1 := by
  have h : ∀ r < 16, ∀ j < 48, src r j < 56 ∧
      64 - pc1At (55 - src r j) = 64 - selAt r (47 - j) ∧ 1 ≤ selAt r (47 - j) ∧
      selAt r (47 - j) ≤ 64 ∧ 1 ≤ pc2.getD (47 - j) 1 := by decide +kernel
  simpa only [pc1At_eq, selAt_eq] using h

theorem roundKey_bit (key : BitVec 64) (r : Nat) (hr : r < 16) (j : Nat) (hj : j < 48) :
    ((expandDesKey key).getD r 0).getLsbD j = key.getLsbD (64 - sel r (47 - j)) := by
  have hsrc := src_sel r hr j hj
  rw [expandDesKey_prefix, stored key 16 (Nat.le_refl _) r hr,
    permute_bit _ _ (by decide) j hj, BitVec.getLsbD_append, ← hsrc.2.1]
  have hb := halves_bit key (r + 1) (by omega_using [hr])
  have hp (u : Nat) (hu : u < 56) : (permute pc1 key).getLsbD u =
      key.getLsbD (64 - pc1.getD (55 - u) 1) := permute_bit pc1 key (by decide) u hu
  unfold src at hsrc ⊢
  by_cases ht : 56 - pc2.getD (47 - j) 1 < 28
  · simp only [ht, ite_true] at hsrc ⊢
    rw [(hb _ ht).2]
    simp only [keyInitial, BitVec.getLsbD_setWidth,
      show (56 - pc2.getD (47 - j) 1 + 448 - tot (r + 1)) % 28 < 28 from Nat.mod_lt _ (by decide),
      decide_true, Bool.true_and]
    exact hp _ hsrc.1
  · simp only [ht, ite_false] at hsrc ⊢
    have h56 : 56 - pc2.getD (47 - j) 1 - 28 < 28 := by omega_using [ht, hsrc.2.2.2.2]
    rw [(hb _ h56).1]
    simp only [keyInitial, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show (56 - pc2.getD (47 - j) 1 - 28 + 448 - tot (r + 1)) % 28 < 28 from
        Nat.mod_lt _ (by decide), decide_true, Bool.true_and]
    exact hp _ hsrc.1

/-! ## The table and its lookups -/

open VG.AArch64 VG.AArch64.RegUpd

/-- Byte `idx` of the table in four vectors. -/
def pick (t0 t1 t2 t3 : BitVec 128) (idx : Nat) : BitVec 8 :=
  vbyte (if idx / 16 = 0 then t0 else if idx / 16 = 1 then t1 else if idx / 16 = 2 then t2 else t3)
    (idx % 16)

theorem tableByte_pick (v : VReg → BitVec 128) {idx : Nat} (h : idx < 64) :
    tableByte v .v16 idx = pick (v .v16) (v .v17) (v .v18) (v .v19) idx := by
  have hc : idx / 16 = 0 ∨ idx / 16 = 1 ∨ idx / 16 = 2 ∨ idx / 16 = 3 := by omega_using [h]
  rcases hc with e | e | e | e <;> simp only [tableByte, pick, e] <;> rfl

/-- What `tbl` on the table leaves, for the indices `m`. -/
def look (t0 t1 t2 t3 m : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => if (vbyte m i).toNat < 64 then pick t0 t1 t2 t3 (vbyte m i).toNat else 0

theorem exec_look (s : State) (d : VReg) :
    exec (.vop (.tblN false 4 d .v16 d)) s =
      some (s.setV d (look (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19) (s.v d))) := by
  have h : (ofVBytes fun i => if (vbyte (s.v d) i).toNat < 16 * 4 then
      tableByte s.v .v16 (vbyte (s.v d) i).toNat else 0) =
      look (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19) (s.v d) := by
    unfold look
    refine congrArg ofVBytes (funext fun i => ?_)
    by_cases hi : (vbyte (s.v d) i).toNat < 64
    · rw [ite_eq_left hi, ite_eq_left hi, tableByte_pick _ hi]
    · rw [ite_eq_right hi, ite_eq_right hi]
  rw [← h]; rfl

theorem tabWords_length : tabWords.length = 128 := by
  simp only [tabWords, List.length_map, List.length_range]

theorem tabWords_getD (i : Nat) (hi : i < 128) :
    tabWords.getD i 0 = (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := by
  simp only [tabWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem exec_tld (s : State) (t : VReg) (j : Nat) (hj : j < 64)
    (h6 : s.gpr .x6 = s.syms tabName) :
    exec (.ldrqTbl t .x6 (16 * j) tabName tabWords) s = some (s.setV t (tabVec j)) := by
  have hc : s.gpr .x6 = s.syms tabName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧
      16 * j / 8 + 2 ≤ tabWords.length := by
    rw [tabWords_length]; exact ⟨h6, by omega_using [hj], by omega_using [hj], by omega_using [hj]⟩
  have hv : tabWords.getD (16 * j / 8 + 1) 0 ++ tabWords.getD (16 * j / 8) 0 = tabVec j := by
    rw [tabWords_getD _ (by omega_using [hj]), tabWords_getD _ (by omega_using [hj]),
      show (16 * j / 8 + 1) / 2 = j by omega_using [], show (16 * j / 8 + 1) % 2 = 1 by omega_using [],
      show 16 * j / 8 / 2 = j by omega_using [], show 16 * j / 8 % 2 = 0 by omega_using []]
    exact Tbl.ofVDwords_halves (tabVec j)
  change (if _ then _ else _) = _
  rw [ite_eq_left hc, hv]

/-! ## Joining the bits -/

theorem sli_bit (k : Nat) (a b : BitVec 8) (j : Nat) (hj : j < 8) :
    (VShiftOp.sli.eval k 8 a b).getLsbD j = if j < k then a.getLsbD j else b.getLsbD (j - k) := by
  simp only [VShiftOp.eval, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hj, decide_true, Bool.true_and]
  by_cases h : j < k
  · simp [h]
  · simp [h, show j - k < 8 by omega_using [hj]]

/-- The byte whose bit `k` is bit 0 of `t k`, as the seven `sli` make it. -/
def joinB (t : Nat → BitVec 8) : BitVec 8 :=
  VShiftOp.sli.eval 7 8 (VShiftOp.sli.eval 6 8 (VShiftOp.sli.eval 5 8 (VShiftOp.sli.eval 4 8
    (VShiftOp.sli.eval 3 8 (VShiftOp.sli.eval 2 8 (VShiftOp.sli.eval 1 8 (t 0) (t 1)) (t 2)) (t 3))
    (t 4)) (t 5)) (t 6)) (t 7)

theorem joinB_bit (t : Nat → BitVec 8) : ∀ k < 8, (joinB t).getLsbD k = (t k).getLsbD 0 := by
  intro k hk
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_using [hk]
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [joinB, sli_bit, Nat.reduceLT, ↓reduceIte, Nat.sub_self,
      Nat.lt_irrefl]

/-- The vector the seven `sli` leave in `v0`, from the eight lookups. -/
def joinV (l : Nat → BitVec 128) : BitVec 128 :=
  let sli (k : Nat) := VArr.b16.map2 (fun w a b => VShiftOp.sli.eval k w a b)
  sli 7 (sli 6 (sli 5 (sli 4 (sli 3 (sli 2 (sli 1 (l 0) (l 1)) (l 2)) (l 3)) (l 4)) (l 5)) (l 6)) (l 7)

theorem vbyte_joinV (l : Nat → BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (joinV l) e = joinB fun k => vbyte (l k) e := by
  simp only [joinV, VArr.map2, vbyte_ofVBytes _ he, joinB]

/-- Round keys `2 pair` and `2 pair + 1`, as `pairCode` computes them from the table. -/
def pairVec (t0 t1 t2 t3 : BitVec 128) (pair : Nat) : BitVec 128 :=
  joinV fun k => look t0 t1 t2 t3 (tabVec (8 * pair + k))

theorem syms_setV (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).syms = s.syms := rfl

/-- The registers the lookups use. -/
def tmps : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]

def loads (pair : Nat) : List Instr :=
  [.ldrqTbl .v0 .x6 (16 * (8 * pair + 0)) tabName tabWords,
   .ldrqTbl .v1 .x6 (16 * (8 * pair + 1)) tabName tabWords,
   .ldrqTbl .v2 .x6 (16 * (8 * pair + 2)) tabName tabWords,
   .ldrqTbl .v3 .x6 (16 * (8 * pair + 3)) tabName tabWords,
   .ldrqTbl .v4 .x6 (16 * (8 * pair + 4)) tabName tabWords,
   .ldrqTbl .v5 .x6 (16 * (8 * pair + 5)) tabName tabWords,
   .ldrqTbl .v6 .x6 (16 * (8 * pair + 6)) tabName tabWords,
   .ldrqTbl .v7 .x6 (16 * (8 * pair + 7)) tabName tabWords]

def tbls : List Instr :=
  [.vop (.tblN false 4 .v0 .v16 .v0), .vop (.tblN false 4 .v1 .v16 .v1),
   .vop (.tblN false 4 .v2 .v16 .v2), .vop (.tblN false 4 .v3 .v16 .v3),
   .vop (.tblN false 4 .v4 .v16 .v4), .vop (.tblN false 4 .v5 .v16 .v5),
   .vop (.tblN false 4 .v6 .v16 .v6), .vop (.tblN false 4 .v7 .v16 .v7)]

def slis : List Instr :=
  [.vop (.shift .sli .b16 .v0 .v1 1), .vop (.shift .sli .b16 .v0 .v2 2),
   .vop (.shift .sli .b16 .v0 .v3 3), .vop (.shift .sli .b16 .v0 .v4 4),
   .vop (.shift .sli .b16 .v0 .v5 5), .vop (.shift .sli .b16 .v0 .v6 6),
   .vop (.shift .sli .b16 .v0 .v7 7)]

theorem pairCode_eq (pair out : Nat) :
    pairCode pair out = loads pair ++ (tbls ++ (slis ++ ([.strq .v0 .x2 out] : List Instr))) := rfl

theorem exec_sli (s : State) (n : VReg) (k : Nat) (hk : k < 8) :
    exec (.vop (.shift .sli .b16 .v0 n k)) s = some (s.setV .v0
      (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval k w a b) (s.v .v0) (s.v n))) := by
  change Option.map _ (if VShiftOp.ok .sli 8 k = true then _ else _) = _
  rw [ite_eq_left (by simp only [VShiftOp.ok, hk, decide_true])]
  rfl

theorem exec_strq' {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ho, and_self, ite_true,
    Option.bind_some, State.store, h]

theorem VOnly.syms {ds : List VReg} {s s' : State} (h : Tbl.VOnly ds s s') : s'.syms = s.syms := by
  rw [h.1]
theorem VOnly.sp {ds : List VReg} {s s' : State} (h : Tbl.VOnly ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem loads_run (s : State) (pair : Nat) (hp : pair < 8) (h6 : s.gpr .x6 = s.syms tabName) :
    ∃ s', runBlock isa (loads pair) s = some s' ∧ Tbl.VOnly tmps s s' ∧
      s'.v .v0 = tabVec (8 * pair + 0) ∧ s'.v .v1 = tabVec (8 * pair + 1) ∧
      s'.v .v2 = tabVec (8 * pair + 2) ∧ s'.v .v3 = tabVec (8 * pair + 3) ∧
      s'.v .v4 = tabVec (8 * pair + 4) ∧ s'.v .v5 = tabVec (8 * pair + 5) ∧
      s'.v .v6 = tabVec (8 * pair + 6) ∧ s'.v .v7 = tabVec (8 * pair + 7) := by
  let s1 := s.setV .v0 (tabVec (8 * pair + 0))
  have e1 : exec (.ldrqTbl .v0 .x6 (16 * (8 * pair + 0)) tabName tabWords) s = some s1 :=
    exec_tld s .v0 _ (by omega_using [hp]) h6
  let s2 := s1.setV .v1 (tabVec (8 * pair + 1))
  have e2 : exec (.ldrqTbl .v1 .x6 (16 * (8 * pair + 1)) tabName tabWords) s1 = some s2 :=
    exec_tld s1 .v1 _ (by omega_using [hp]) h6
  let s3 := s2.setV .v2 (tabVec (8 * pair + 2))
  have e3 : exec (.ldrqTbl .v2 .x6 (16 * (8 * pair + 2)) tabName tabWords) s2 = some s3 :=
    exec_tld s2 .v2 _ (by omega_using [hp]) h6
  let s4 := s3.setV .v3 (tabVec (8 * pair + 3))
  have e4 : exec (.ldrqTbl .v3 .x6 (16 * (8 * pair + 3)) tabName tabWords) s3 = some s4 :=
    exec_tld s3 .v3 _ (by omega_using [hp]) h6
  let s5 := s4.setV .v4 (tabVec (8 * pair + 4))
  have e5 : exec (.ldrqTbl .v4 .x6 (16 * (8 * pair + 4)) tabName tabWords) s4 = some s5 :=
    exec_tld s4 .v4 _ (by omega_using [hp]) h6
  let s6 := s5.setV .v5 (tabVec (8 * pair + 5))
  have e6 : exec (.ldrqTbl .v5 .x6 (16 * (8 * pair + 5)) tabName tabWords) s5 = some s6 :=
    exec_tld s5 .v5 _ (by omega_using [hp]) h6
  let s7 := s6.setV .v6 (tabVec (8 * pair + 6))
  have e7 : exec (.ldrqTbl .v6 .x6 (16 * (8 * pair + 6)) tabName tabWords) s6 = some s7 :=
    exec_tld s6 .v6 _ (by omega_using [hp]) h6
  let s8 := s7.setV .v7 (tabVec (8 * pair + 7))
  have e8 : exec (.ldrqTbl .v7 .x6 (16 * (8 * pair + 7)) tabName tabWords) s7 = some s8 :=
    exec_tld s7 .v7 _ (by omega_using [hp]) h6
  have o1 : Tbl.VOnly tmps s s1 := Tbl.VOnly.setV _ (by decide) _
  have o2 : Tbl.VOnly tmps s s2 := o1.trans (Tbl.VOnly.setV _ (by decide) _)
  have o3 : Tbl.VOnly tmps s s3 := o2.trans (Tbl.VOnly.setV _ (by decide) _)
  have o4 : Tbl.VOnly tmps s s4 := o3.trans (Tbl.VOnly.setV _ (by decide) _)
  have o5 : Tbl.VOnly tmps s s5 := o4.trans (Tbl.VOnly.setV _ (by decide) _)
  have o6 : Tbl.VOnly tmps s s6 := o5.trans (Tbl.VOnly.setV _ (by decide) _)
  have o7 : Tbl.VOnly tmps s s7 := o6.trans (Tbl.VOnly.setV _ (by decide) _)
  have o8 : Tbl.VOnly tmps s s8 := o7.trans (Tbl.VOnly.setV _ (by decide) _)
  refine ⟨s8, by rw [loads, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some, runBlock_nil], o8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [s8, s7, s6, s5, s4, s3, s2, s1, v_setV, reduceCtorEq, ↓reduceIte]

theorem tbls_run (s : State) :
    ∃ s', runBlock isa tbls s = some s' ∧ Tbl.VOnly tmps s s' ∧
      (∀ r ∈ tmps, s'.v r = look (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19) (s.v r)) := by
  let s1 := s.setV .v0 (look (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19) (s.v .v0))
  have e1 : exec (.vop (.tblN false 4 .v0 .v16 .v0)) s = some s1 := exec_look s .v0
  let s2 := s1.setV .v1 (look (s1.v .v16) (s1.v .v17) (s1.v .v18) (s1.v .v19) (s1.v .v1))
  have e2 : exec (.vop (.tblN false 4 .v1 .v16 .v1)) s1 = some s2 := exec_look s1 .v1
  let s3 := s2.setV .v2 (look (s2.v .v16) (s2.v .v17) (s2.v .v18) (s2.v .v19) (s2.v .v2))
  have e3 : exec (.vop (.tblN false 4 .v2 .v16 .v2)) s2 = some s3 := exec_look s2 .v2
  let s4 := s3.setV .v3 (look (s3.v .v16) (s3.v .v17) (s3.v .v18) (s3.v .v19) (s3.v .v3))
  have e4 : exec (.vop (.tblN false 4 .v3 .v16 .v3)) s3 = some s4 := exec_look s3 .v3
  let s5 := s4.setV .v4 (look (s4.v .v16) (s4.v .v17) (s4.v .v18) (s4.v .v19) (s4.v .v4))
  have e5 : exec (.vop (.tblN false 4 .v4 .v16 .v4)) s4 = some s5 := exec_look s4 .v4
  let s6 := s5.setV .v5 (look (s5.v .v16) (s5.v .v17) (s5.v .v18) (s5.v .v19) (s5.v .v5))
  have e6 : exec (.vop (.tblN false 4 .v5 .v16 .v5)) s5 = some s6 := exec_look s5 .v5
  let s7 := s6.setV .v6 (look (s6.v .v16) (s6.v .v17) (s6.v .v18) (s6.v .v19) (s6.v .v6))
  have e7 : exec (.vop (.tblN false 4 .v6 .v16 .v6)) s6 = some s7 := exec_look s6 .v6
  let s8 := s7.setV .v7 (look (s7.v .v16) (s7.v .v17) (s7.v .v18) (s7.v .v19) (s7.v .v7))
  have e8 : exec (.vop (.tblN false 4 .v7 .v16 .v7)) s7 = some s8 := exec_look s7 .v7
  have o1 : Tbl.VOnly tmps s s1 := Tbl.VOnly.setV _ (by decide) _
  have o2 : Tbl.VOnly tmps s s2 := o1.trans (Tbl.VOnly.setV _ (by decide) _)
  have o3 : Tbl.VOnly tmps s s3 := o2.trans (Tbl.VOnly.setV _ (by decide) _)
  have o4 : Tbl.VOnly tmps s s4 := o3.trans (Tbl.VOnly.setV _ (by decide) _)
  have o5 : Tbl.VOnly tmps s s5 := o4.trans (Tbl.VOnly.setV _ (by decide) _)
  have o6 : Tbl.VOnly tmps s s6 := o5.trans (Tbl.VOnly.setV _ (by decide) _)
  have o7 : Tbl.VOnly tmps s s7 := o6.trans (Tbl.VOnly.setV _ (by decide) _)
  have o8 : Tbl.VOnly tmps s s8 := o7.trans (Tbl.VOnly.setV _ (by decide) _)
  refine ⟨s8, by rw [tbls, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some, runBlock_nil], o8, ?_⟩
  simp only [tmps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [s8, s7, s6, s5, s4, s3, s2, s1, v_setV, reduceCtorEq, ↓reduceIte]

theorem slis_run (s : State) :
    ∃ s', runBlock isa slis s = some s' ∧ Tbl.VOnly tmps s s' ∧
      s'.v .v0 = joinV fun k => s.v (tmp k) := by
  let s1 := s.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 1 w a b) (s.v .v0) (s.v .v1))
  have e1 : exec (.vop (.shift .sli .b16 .v0 .v1 1)) s = some s1 := exec_sli s .v1 1 (by decide)
  let s2 := s1.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 2 w a b) (s1.v .v0) (s1.v .v2))
  have e2 : exec (.vop (.shift .sli .b16 .v0 .v2 2)) s1 = some s2 := exec_sli s1 .v2 2 (by decide)
  let s3 := s2.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 3 w a b) (s2.v .v0) (s2.v .v3))
  have e3 : exec (.vop (.shift .sli .b16 .v0 .v3 3)) s2 = some s3 := exec_sli s2 .v3 3 (by decide)
  let s4 := s3.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 4 w a b) (s3.v .v0) (s3.v .v4))
  have e4 : exec (.vop (.shift .sli .b16 .v0 .v4 4)) s3 = some s4 := exec_sli s3 .v4 4 (by decide)
  let s5 := s4.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 5 w a b) (s4.v .v0) (s4.v .v5))
  have e5 : exec (.vop (.shift .sli .b16 .v0 .v5 5)) s4 = some s5 := exec_sli s4 .v5 5 (by decide)
  let s6 := s5.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 6 w a b) (s5.v .v0) (s5.v .v6))
  have e6 : exec (.vop (.shift .sli .b16 .v0 .v6 6)) s5 = some s6 := exec_sli s5 .v6 6 (by decide)
  let s7 := s6.setV .v0 (VArr.b16.map2 (fun w a b => VShiftOp.sli.eval 7 w a b) (s6.v .v0) (s6.v .v7))
  have e7 : exec (.vop (.shift .sli .b16 .v0 .v7 7)) s6 = some s7 := exec_sli s6 .v7 7 (by decide)
  have o1 : Tbl.VOnly tmps s s1 := Tbl.VOnly.setV _ (by decide) _
  have o2 : Tbl.VOnly tmps s s2 := o1.trans (Tbl.VOnly.setV _ (by decide) _)
  have o3 : Tbl.VOnly tmps s s3 := o2.trans (Tbl.VOnly.setV _ (by decide) _)
  have o4 : Tbl.VOnly tmps s s4 := o3.trans (Tbl.VOnly.setV _ (by decide) _)
  have o5 : Tbl.VOnly tmps s s5 := o4.trans (Tbl.VOnly.setV _ (by decide) _)
  have o6 : Tbl.VOnly tmps s s6 := o5.trans (Tbl.VOnly.setV _ (by decide) _)
  have o7 : Tbl.VOnly tmps s s7 := o6.trans (Tbl.VOnly.setV _ (by decide) _)
  refine ⟨s7, by rw [slis, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil], o7, ?_⟩
  simp only [s7, s6, s5, s4, s3, s2, s1, v_setV, reduceCtorEq, ↓reduceIte, joinV, tmp,
    List.getD_cons_zero, List.getD_cons_succ]

/-- `pairCode` stores `pairVec` and keeps everything but `v0`–`v7`. -/
theorem pair_run (s : State) (pair out : Nat) (hp : pair < 8) (ho : out % 16 = 0 ∧ out < 65536)
    (h6 : s.gpr .x6 = s.syms tabName)
    (hw : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 out) 16) :
    ∃ s', runBlock isa (pairCode pair out) s = some s' ∧
      s'.mem = s.mem.write (s.gpr .x2 + BitVec.ofNat 64 out) 16
        (pairVec (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19) pair) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ s'.sp = s.sp ∧
      s'.v .v16 = s.v .v16 ∧ s'.v .v17 = s.v .v17 ∧ s'.v .v18 = s.v .v18 ∧ s'.v .v19 = s.v .v19 := by
  obtain ⟨a, ra, oa, a0, a1, a2, a3, a4, a5, a6, a7⟩ := loads_run s pair hp h6
  obtain ⟨b, rb, ob, hb⟩ := tbls_run a
  obtain ⟨c, rc, oc, hc⟩ := slis_run b
  have o := (oa.trans ob).trans oc
  have hw' : InRegions c.wr (c.gpr .x2 + BitVec.ofNat 64 out) 16 := by rw [o.wr, o.gpr]; exact hw
  have keep (r : VReg) (hr : r ∉ tmps) : c.v r = s.v r := o.2 r hr
  have ka (r : VReg) (hr : r ∉ tmps) : a.v r = s.v r := oa.2 r hr
  refine ⟨{ c with mem := c.mem.write (c.gpr .x2 + BitVec.ofNat 64 out) 16 (c.v .v0) }, by
    rw [pairCode_eq]
    exact Tbl.runBlock_cat_some ra (Tbl.runBlock_cat_some rb (Tbl.runBlock_cat_some rc (by
      rw [runBlock_cons, exec_strq' ho hw', runStep_some, runBlock_nil]))), ?_,
    o.gpr, o.rd, o.wr, VOnly.syms (s' := c) o, VOnly.sp (s' := c) o, keep _ (by decide), keep _ (by decide),
    keep _ (by decide), keep _ (by decide)⟩
  show c.mem.write (c.gpr .x2 + BitVec.ofNat 64 out) 16 (c.v .v0) = _
  rw [o.mem, o.gpr, hc]
  simp only [pairVec, joinV, tmp, List.getD_cons_zero, List.getD_cons_succ]
  rw [hb .v0 (by decide), hb .v1 (by decide), hb .v2 (by decide), hb .v3 (by decide),
    hb .v4 (by decide), hb .v5 (by decide), hb .v6 (by decide), hb .v7 (by decide),
    a0, a1, a2, a3, a4, a5, a6, a7, ka .v16 (by decide), ka .v17 (by decide), ka .v18 (by decide),
    ka .v19 (by decide)]

/-! ## The round keys in the vector -/

/-- The table of the component key whose bytes, the first lowest, are the word `K`:
bit 0 of its byte `t` is bit `t / 8` of byte `t % 8`. -/
def Tab (K : BitVec 64) (t0 t1 t2 t3 : BitVec 128) : Prop :=
  ∀ t < 64, (pick t0 t1 t2 t3 t).getLsbD 0 = K.getLsbD (8 * (t % 8) + t / 8)

theorem keyIndex_facts (p : Nat) (h1 : 1 ≤ p) (h2 : p ≤ 64) :
    keyIndex p < 64 ∧ keyIndex p % 8 = (p - 1) / 8 ∧ keyIndex p / 8 = 7 - (p - 1) % 8 := by
  unfold keyIndex; omega_using [h1, h2]

theorem vbyte_tabVec (pair k b : Nat) (hk : k < 8) (hb : b < 16) :
    vbyte (tabVec (8 * pair + k)) b = idxByte pair k b := by
  rw [tabVec, vbyte_ofVBytes _ hb, show (8 * pair + k) / 8 = pair by omega_using [hk],
    show (8 * pair + k) % 8 = k by omega_using [hk]]

theorem pairVec_dword (K : BitVec 64) (t0 t1 t2 t3 : BitVec 128) (hT : Tab K t0 t1 t2 t3)
    (pair h : Nat) (hp : pair < 8) (hh : h < 2) :
    vdword (pairVec t0 t1 t2 t3 pair) h =
      ((expandDesKey (rev64 K)).getD (2 * pair + h) 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : 8 * h + i / 8 < 16 := by omega_using [hh, hi]
  have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have lhs : (vdword (pairVec t0 t1 t2 t3 pair) h).getLsbD i =
      (vbyte (pairVec t0 t1 t2 t3 pair) (8 * h + i / 8)).getLsbD (i % 8) := by
    simp only [vdword, vbyte, BitVec.getLsbD_extractLsb', hi, hk, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [])
  rw [lhs, pairVec, vbyte_joinV _ hb, joinB_bit _ _ hk, look, vbyte_ofVBytes _ hb,
    vbyte_tabVec _ _ _ hk hb, idxByte, show (8 * h + i / 8) % 8 = i / 8 by omega_using [hi],
    show (8 * h + i / 8) / 8 = h by omega_using [hi], show 8 * (i / 8) + i % 8 = i by omega_using [],
    BitVec.getLsbD_setWidth]
  by_cases h48 : i < 48
  · have hs := src_sel (2 * pair + h) (by omega_using [hp, hh]) i h48
    obtain ⟨hlt, hmod, hdiv⟩ := keyIndex_facts _ hs.2.2.1 hs.2.2.2.1
    have hn : (BitVec.ofNat 8 (keyIndex (sel (2 * pair + h) (47 - i)))).toNat =
        keyIndex (sel (2 * pair + h) (47 - i)) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hlt])
    simp only [show i / 8 < 6 from by omega_using [h48], ↓reduceIte, hn, hlt]
    rw [hT _ hlt, hmod, hdiv, roundKey_bit _ _ (by omega_using [hp, hh]) _ h48,
      getLsbD_rev64 _ (by omega_using [hs.2.2.1])]
    simp only [hi, decide_true, Bool.true_and]
    exact congrArg K.getLsbD (by omega_using [hs.2.2.1, hs.2.2.2.1])
  · simp only [show ¬ i / 8 < 6 from by omega_using [h48], ↓reduceIte,
      show ¬ (0xFF : BitVec 8).toNat < 64 from by decide,
      BitVec.getLsbD_of_ge _ _ (show 48 ≤ i by omega_using [h48]), Bool.and_false]
    rfl

/-! ## The eight pairs of a component -/

/-- After the first `n` pairs of a component whose table is of `K`, at `base`. -/
structure PairsPost (K : BitVec 64) (base : Addr) (n : Nat) (s s' : State) : Prop where
  keys : ∀ i < 2 * n, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((expandDesKey (rev64 K)).getD i 0).setWidth 64
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  sp : s'.sp = s.sp
  v16 : s'.v .v16 = s.v .v16
  v17 : s'.v .v17 = s.v .v17
  v18 : s'.v .v18 = s.v .v18
  v19 : s'.v .v19 = s.v .v19
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem pairs_ok (s : State) (index : Nat) (hc : index < 3) (K : BitVec 64)
    (hT : Tab K (s.v .v16) (s.v .v17) (s.v .v18) (s.v .v19)) (h6 : s.gpr .x6 = s.syms tabName)
    (hw : ∀ pair < 8, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * index) + BitVec.ofNat 64 (16 * pair)) 16) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun pair =>
      pairCode pair (128 * index + 16 * pair))) s
      (PairsPost K (s.gpr .x2 + BitVec.ofNat 64 (128 * index)) n s) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact WP.of_runBlock ⟨s, rfl, fun i hi => absurd hi (by omega_using []), rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    intro hn
    have hn8 : n < 8 := by omega_using [hn]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun a ha => ?_
    have hT' : Tab K (a.v .v16) (a.v .v17) (a.v .v18) (a.v .v19) := by
      rw [ha.v16, ha.v17, ha.v18, ha.v19]; exact hT
    have hwa : InRegions a.wr (a.gpr .x2 + BitVec.ofNat 64 (128 * index + 16 * n)) 16 := by
      rw [ha.wr, ha.gpr, ← Offset.add_add]; exact hw n hn8
    obtain ⟨b, rb, hm, hg, hrd, hwr, hsy, hsp, b16, b17, b18, b19⟩ :=
      pair_run a n (128 * index + 16 * n) hn8 (by omega_using [hc, hn8])
        (by rw [ha.gpr, ha.syms]; exact h6) hwa
    refine WP.of_runBlock ⟨b, rb, ?_⟩
    have d0 := pairVec_dword K _ _ _ _ hT' n 0 hn8 (by decide)
    have d1 := pairVec_dword K _ _ _ _ hT' n 1 hn8 (by decide)
    rw [ha.gpr, ← Offset.add_add] at hm
    generalize pairVec (a.v .v16) (a.v .v17) (a.v .v18) (a.v .v19) n = V at hm d0 d1
    generalize s.gpr .x2 + BitVec.ofNat 64 (128 * index) = base at hm ha ⊢
    have hmem : b.mem = (a.mem.writeW (base + BitVec.ofNat 64 (16 * n)) (vdword V 0)).writeW
        (base + BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 8) (vdword V 1) := by
      rw [hm, ← write16_dwords]
      exact congrArg _ (Tbl.ofVDwords_halves V).symm
    rw [Offset.add_add] at hmem
    have hfr : Frame [⟨base, 128⟩] a.mem b.mem := by
      rw [hmem]
      exact ((Frame.refl _ _).writeW (r := ⟨base, 128⟩) (by simp) _
        (Offset.contains_base _ (by omega_using [hn8]) (by omega_using [hn8]))).writeW
        (r := ⟨base, 128⟩) (by simp) _
        (Offset.contains_base _ (by omega_using [hn8]) (by omega_using [hn8]))
    refine ⟨fun i hi => ?_, hg.trans ha.gpr, hrd.trans ha.rd, hwr.trans ha.wr, hsy.trans ha.syms,
      hsp.trans ha.sp, b16.trans ha.v16, b17.trans ha.v17, b18.trans ha.v18, b19.trans ha.v19,
      ha.frame.trans hfr⟩
    rw [hmem]
    by_cases h0 : i < 2 * n
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [h0])) (by omega_using [hn8, h0])
        (by omega_using [hn8])) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [h0])) (by omega_using [hn8, h0])
        (by omega_using [hn8])) (by decide)]
      exact ha.keys i h0
    · by_cases h1 : i = 2 * n
      · subst h1
        rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [])) (by omega_using [hn8])
          (by omega_using [hn8])) (by decide), show 8 * (2 * n) = 16 * n by omega_using [],
          Mem.readW_writeW_self64, d0]
        rfl
      · obtain rfl : i = 2 * n + 1 := by omega_using [hi, h0, h1]
        rw [show 8 * (2 * n + 1) = 16 * n + 8 by omega_using [], Mem.readW_writeW_self64, d1]

/-! ## The table of a component key -/

theorem tab_bit (A B : BitVec 64) (e : Nat) :
    (vbyte (ofVDwords A B) e).getLsbD 0 =
      if e < 8 then A.getLsbD (8 * e) else B.getLsbD (8 * (e - 8)) := by
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.add_zero,
    show (0 : Nat) < 8 by decide, decide_true, Bool.true_and]
  by_cases h : e < 8
  · rw [ite_eq_left (by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_right (by omega_using [h]), ite_eq_right h]
    exact congrArg B.getLsbD (by omega_using [h])

theorem exec_ushr (s : State) (d : VReg) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 64) :
    exec (.vop (.shift .ushr .d2 d .v16 k)) s = some (s.setV d
      (ofVDwords (vdword (s.v .v16) 0 >>> k) (vdword (s.v .v16) 1 >>> k))) := by
  change Option.map _ (if VShiftOp.ok .ushr 64 k = true then _ else _) = _
  rw [ite_eq_left (by simp only [VShiftOp.ok, hk.1, hk.2, decide_true, Bool.and_self])]
  rfl

/-- `spread` leaves the table of the word at `x0 + offset` in `v16`–`v19`. -/
theorem spread_run (s : State) (offset : Nat) (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8) :
    ∃ s', runBlock isa (spread offset) s = some s' ∧
      Tab (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 offset) 64)
        (s'.v .v16) (s'.v .v17) (s'.v .v18) (s'.v .v19) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) := by
  generalize hK : s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 offset) 64 = K
  let s1 := s.write .x .x4 K
  let s2 := s1.write .x .x5 (K >>> 1)
  let s3 := s2.setV .v16 (setLane (s2.v .v16) 64 0 (s2.gpr .x4))
  let s4 := s3.setV .v16 (setLane (s3.v .v16) 64 1 (s3.gpr .x5))
  let s5 := s4.setV .v17 (ofVDwords (vdword (s4.v .v16) 0 >>> 2) (vdword (s4.v .v16) 1 >>> 2))
  let s6 := s5.setV .v18 (ofVDwords (vdword (s5.v .v16) 0 >>> 4) (vdword (s5.v .v16) 1 >>> 4))
  let s7 := s6.setV .v19 (ofVDwords (vdword (s6.v .v16) 0 >>> 6) (vdword (s6.v .v16) 1 >>> 6))
  have e1 : exec (.ldr .x .x4 .x0 offset) s = some s1 := by rw [exec_ldr_x ho hr, hK]
  have e2 : exec (.lsr .x .x5 .x4 1) s1 = some s2 := by
    rw [exec_lsr_x (by decide)]
    simp only [s2, s1, State.read, gpr_write_self, BitVec.setWidth_eq]
  have e3 : exec (.vop (.ins .d2 .v16 0 .x4)) s2 = some s3 := Tbl.exec_insd _ _ _ (by decide) _
  have e4 : exec (.vop (.ins .d2 .v16 1 .x5)) s3 = some s4 := Tbl.exec_insd _ _ _ (by decide) _
  have e5 : exec (.vop (.shift .ushr .d2 .v17 .v16 2)) s4 = some s5 := exec_ushr _ _ _ (by decide)
  have e6 : exec (.vop (.shift .ushr .d2 .v18 .v16 4)) s5 = some s6 := exec_ushr _ _ _ (by decide)
  have e7 : exec (.vop (.shift .ushr .d2 .v19 .v16 6)) s6 = some s7 := exec_ushr _ _ _ (by decide)
  have h16 : s4.v .v16 = ofVDwords K (K >>> 1) := by
    simp only [s4, s3, s2, s1, v_setV, ↓reduceIte, gpr_setV, gpr_write, reduceCtorEq,
      BitVec.setWidth_eq]
    exact setLane_two _ _ _
  have t16 : s7.v .v16 = ofVDwords K (K >>> 1) := by
    simp only [s7, s6, s5, v_setV, reduceCtorEq, ↓reduceIte]; exact h16
  have t17 : s7.v .v17 = ofVDwords (K >>> 2) (K >>> 1 >>> 2) := by
    simp only [s7, s6, s5, v_setV, reduceCtorEq, ↓reduceIte, h16, vdword_ofVDwords_0,
      vdword_ofVDwords_1]
  have t18 : s7.v .v18 = ofVDwords (K >>> 4) (K >>> 1 >>> 4) := by
    simp only [s7, s6, s5, v_setV, reduceCtorEq, ↓reduceIte, h16, vdword_ofVDwords_0,
      vdword_ofVDwords_1]
  have t19 : s7.v .v19 = ofVDwords (K >>> 6) (K >>> 1 >>> 6) := by
    simp only [s7, s6, s5, v_setV, reduceCtorEq, ↓reduceIte, h16, vdword_ofVDwords_0,
      vdword_ofVDwords_1]
  refine ⟨s7, by
    rw [spread, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons,
      e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil], ?_, rfl, rfl, rfl, rfl, rfl,
    fun r h4 h5 => ?_⟩
  · intro t ht
    rw [t16, t17, t18, t19, pick]
    have hc : t / 16 = 0 ∨ t / 16 = 1 ∨ t / 16 = 2 ∨ t / 16 = 3 := by omega_using [ht]
    rcases hc with e | e | e | e <;>
      simp only [e, ↓reduceIte, Nat.reduceEqDiff, tab_bit, BitVec.getLsbD_ushiftRight] <;>
      (by_cases h8 : t % 16 < 8
       · rw [ite_eq_left h8]; exact congrArg K.getLsbD (by omega_using [e, h8])
       · rw [ite_eq_right h8]; exact congrArg K.getLsbD (by omega_using [e, h8]))
  · simp only [s7, s6, s5, s4, s3, s2, s1, gpr_setV, gpr_write, h4, h5, ↓reduceIte]

/-! ## A component -/

/-- A component's sixteen round keys, at `base`. -/
structure ComponentPost (keys : DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  sp : s'.sp = s.sp
  reg : ∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset index : Nat) (hc : index < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768) (h6 : s.gpr .x6 = s.syms tabName)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ pair < 8, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * index) + BitVec.ofNat 64 (16 * pair)) 16) :
    WP isa (component offset index) s
      (ComponentPost (expandDesKey (decodeBlock (blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset))))
        (s.gpr .x2 + BitVec.ofNat 64 (128 * index)) s) := by
  obtain ⟨a, ra, hT, am, ard, awr, asy, asp, ag⟩ := spread_run s offset ho hr
  rw [component, WP.block_append_iff]
  refine WP.of_runBlock ⟨a, ra, ?_⟩
  have h2 : a.gpr .x2 = s.gpr .x2 := ag _ (by decide) (by decide)
  have hp := pairs_ok a index hc _ hT (by rw [ag _ (by decide) (by decide), asy]; exact h6)
    (by rw [awr, h2]; exact hw) 8 (Nat.le_refl _)
  rw [h2] at hp
  refine WP.mono hp fun b hb => ⟨fun i hi => ?_, hb.rd.trans ard, hb.wr.trans awr,
    hb.syms.trans asy, hb.sp.trans asp, fun r h4 h5 => ?_, ?_⟩
  · rw [decodeBlock_readW]; exact hb.keys i (by omega_using [hi])
  · rw [hb.gpr]; exact ag r h4 h5
  · rw [← am]; exact hb.frame

end VG.Proof.TripleDes.AArch64.Key

/-! ### `TripleDes.AArch64.Key.Copy`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x4)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x4 src a, .str .x .x4 dst b] s = some s' ∧
      Keep [.x4] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x ha readable, runStep_some,
      runBlock_cons, exec_str_x hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x4 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .x2) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega_using [hn]))
    intro s₁ h₁
    have hbase : s₁.gpr .x2 = s.gpr .x2 := h₁.reg .x2 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega_using [hn])
    have writable : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega_using [hn])
    obtain ⟨s₂, run₂, keep₂⟩ := copy64_ok s₁ .x2 .x2
      (8 * n) (256 + 8 * n) (by decide) readable writable (by omega_using [hn]) (by omega_using [hn])
    have source : s₁.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .x2) (by omega_using [hn]) (by omega_using [hn]) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x2) (by omega_using [he]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact h₁.keys i (by omega_using [hi, he])
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .x2 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega_using [hn]) (by omega_using [hn])
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.AArch64.Key

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes (componentKeys componentOffset)
open VG.Impl.TripleDes.AArch64.Key (tabName)

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .x2, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .x2) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .x1).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset n, offset + n ≤ 384 → InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 offset) n
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .x1).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c) (h6 : s.gpr .x6 = s.syms tabName)
    (hoff : componentOffset (origin.gpr .x1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.AArch64.Key.component (8 * c) c) s
      (fun t => Components origin t (c + 1) ∧ t.gpr .x6 = t.syms tabName) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .x0 (by decide) (by decide) (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ pair < 8, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (16 * pair)) 16 := by
    intro j hj
    rw [hs.wr, hs.reg .x2 (by decide) (by decide) (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega_using [hc]) h6 read write)
  intro t ht
  have x2 := hs.reg .x2 (by decide) (by decide) (by decide)
  have x0 := hs.reg .x0 (by decide) (by decide) (by decide)
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [x2] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .x0 + BitVec.ofNat 64 (8 * c)) := by
    rw [x0]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r h4 h5 h6' => (ht.reg r h4 h5).trans (hs.reg r h4 h5 h6'), hs.frame.trans (frame.sub ?_)⟩,
    by rw [ht.reg .x6 (by decide) (by decide), ht.syms]; exact h6⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, x2, Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .x2) k j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .x2) k j) (w := 64) (r := ⟨slot (origin.gpr .x2) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .x1).toNat = 16) :
    WP isa (.block Impl.TripleDes.AArch64.Key.copyThird) s (Components origin · 3) := by
  have reads : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hs.rd, hs.wr, hs.reg .x2 (by decide) (by decide) (by decide)]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i) 8 (by omega_using [hi])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8 := by
    intro i hi
    rw [hs.wr, hs.reg .x2 (by decide) (by decide) (by decide)]
    exact hp.writes _ _ (by omega_using [hi])
  apply WP.mono (copy_ok s 16 (by decide) reads writes)
  intro t ht
  have frame : Frame [⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .x2 (by decide) (by decide) (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 2 =
          componentKeys origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .x2 (by decide) (by decide) (by decide)] at h
      change t.mem.readW (origin.gpr .x2 + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .x2) c j) 8).Disjoint
          ⟨origin.gpr .x2 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot (origin.gpr .x2) c j) (w := 64) (r := ⟨slot (origin.gpr .x2) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r h4 h5 h6
    exact (ht.reg r h4).trans (hs.reg r h4 h5 h6)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .x2) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .x0) (origin.gpr .x1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .x2) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.AArch64.Key
