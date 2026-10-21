module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym

/-!
# ML-KEM on AArch64: the NTT halfword by halfword, what the terms mean

A term holds of a halfword (`Hd`) when it is not followed or the halfword is
its value (`T.eval`), given the coefficients after each number of layers (`L`)
and their reduced values (`O`), which obey the butterflies and the reduction
(`Model`). The operations of the machine keep this (`mulT_ok`, `addT_ok`, …),
and so do the packed numbers it keeps them in (`slot_upd`, `get_ofFn`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-! ## Packed numbers -/

theorem ndiv (a b : Nat) : Nat.div a b = a / b := rfl
theorem nmod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem slot_def (w n i : Nat) : slot w n i = n / 2 ^ (w * i) % 2 ^ w := rfl

theorem upd_def (w n i x : Nat) : upd w n i x = n - slot w n i * 2 ^ (w * i) + x * 2 ^ (w * i) := rfl

/-- `u = A + P x + P M Q`. -/
theorem div_parts {A P x M Q : Nat} (hA : A < P) (hx : x < M) :
    (A + P * x + P * M * Q) / P = x + M * Q ∧ (A + P * x + P * M * Q) / (P * M) = Q := by
  have hP : 0 < P := by omega
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hA,
      Nat.zero_add]
  · have hAx : A + P * x < P * M := by
      calc A + P * x < P + P * x := by omega
        _ = P * (x + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        _ ≤ P * M := Nat.mul_le_mul_left _ hx
    rw [Nat.add_mul_div_left _ _ (Nat.mul_pos hP hM), Nat.div_eq_of_lt hAx, Nat.zero_add]

theorem pow_split (w i j : Nat) (h : i ≤ j) : 2 ^ (w * j) = 2 ^ (w * i) * 2 ^ (w * (j - i)) := by
  rw [← Nat.pow_add, ← Nat.mul_add, Nat.add_sub_cancel' h]

theorem slot_parts {w i A x Q : Nat} (hA : A < 2 ^ (w * i)) (hx : x < 2 ^ w) (j : Nat) :
    slot w (A + 2 ^ (w * i) * x + 2 ^ (w * i) * 2 ^ w * Q) j =
      if j < i then slot w A j else if j = i then x else slot w Q (j - (i + 1)) := by
  rw [slot_def, slot_def]
  have hP := Nat.two_pow_pos (w * i)
  have hM := Nat.two_pow_pos w
  obtain ⟨d1, d2⟩ := div_parts (Q := Q) hA hx
  split
  · rename_i hj
    -- `2 ^ (w * i) = 2 ^ (w * j) * 2 ^ w * R`
    have e : 2 ^ (w * i) = 2 ^ (w * j) * (2 ^ w * 2 ^ (w * (i - (j + 1)))) := by
      rw [← Nat.pow_add, ← Nat.pow_add, show w + w * (i - (j + 1)) = w * (i - j) by
        rw [show i - j = (i - (j + 1)) + 1 by omega, Nat.mul_succ, Nat.add_comm], ← Nat.mul_add,
        Nat.add_sub_cancel' (Nat.le_of_lt hj)]
    have hJ := Nat.two_pow_pos (w * j)
    rw [show A + 2 ^ (w * i) * x + 2 ^ (w * i) * 2 ^ w * Q = A + 2 ^ (w * j) * (2 ^ w * (2 ^ (w * (i - (j + 1)))
        * (x + 2 ^ w * Q))) by rw [Nat.add_assoc, e]; grind,
      Nat.add_mul_div_left _ _ hJ, Nat.add_mul_mod_self_left]
  · split
    · rename_i _ hj
      subst hj
      rw [d1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    · rename_i h1 h2
      rw [pow_split w (i + 1) j (by omega), show 2 ^ (w * (i + 1)) = 2 ^ (w * i) * 2 ^ w by
          rw [Nat.mul_succ, Nat.pow_add], ← Nat.div_div_eq_div_mul, d2]
      rfl

theorem split_slot (w n i : Nat) :
    n = n % 2 ^ (w * i) + 2 ^ (w * i) * slot w n i + 2 ^ (w * i) * 2 ^ w * (n / (2 ^ (w * i) * 2 ^ w)) := by
  rw [slot_def]
  have h1 := Nat.mod_add_div n (2 ^ (w * i))
  have h2 := Nat.mod_add_div (n / 2 ^ (w * i)) (2 ^ w)
  rw [Nat.div_div_eq_div_mul] at h2
  rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, h2, h1]

theorem upd_parts (w n i x : Nat) :
    upd w n i x = n % 2 ^ (w * i) + 2 ^ (w * i) * x + 2 ^ (w * i) * 2 ^ w * (n / (2 ^ (w * i) * 2 ^ w)) := by
  have h := split_slot w n i
  rw [upd_def]
  generalize n % 2 ^ (w * i) = A at h ⊢
  generalize slot w n i = s at h ⊢
  generalize n / (2 ^ (w * i) * 2 ^ w) = Q at h ⊢
  rw [Nat.mul_comm s, Nat.mul_comm x]
  omega

theorem slot_upd (w n i x : Nat) (hx : x < 2 ^ w) (j : Nat) :
    slot w (upd w n i x) j = if j = i then x else slot w n j := by
  have hA := Nat.mod_lt n (Nat.two_pow_pos (w * i))
  have hs : slot w n i < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  rw [upd_parts, slot_parts hA hx]
  conv => rhs; rw [split_slot w n i, slot_parts hA hs]
  by_cases h : j < i
  · simp [h, show j ≠ i by omega]
  · by_cases h' : j = i
    · simp [h']
    · simp [h, h']

theorem slot_zero_cons {w d r : Nat} (hd : d < 2 ^ w) : slot w (d + 2 ^ w * r) 0 = d := by
  rw [slot_def, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

theorem slot_succ_cons {w d r : Nat} (hd : d < 2 ^ w) (i : Nat) : slot w (d + 2 ^ w * r) (i + 1) = slot w r i := by
  rw [slot_def, slot_def, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * i)), ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hd, Nat.zero_add]

theorem slot_lt' {w d : Nat} (hd : d < 2 ^ w) : slot w d 0 = d := by
  rw [slot_def, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hd]

theorem ofFn_eq (f : Nat → T) : Y.ofFn f =
    f 0 % 2 ^ tw + 2 ^ tw * (f 1 % 2 ^ tw + 2 ^ tw * (f 2 % 2 ^ tw + 2 ^ tw * (f 3 % 2 ^ tw +
    2 ^ tw * (f 4 % 2 ^ tw + 2 ^ tw * (f 5 % 2 ^ tw + 2 ^ tw * (f 6 % 2 ^ tw + 2 ^ tw * (f 7 % 2 ^ tw))))))) := rfl

theorem get_ofFn (f : Nat → T) {e : Nat} (he : e < 8) : (Y.ofFn f).get e = f e % 2 ^ tw := by
  have hm : ∀ a, a % 2 ^ tw < 2 ^ tw := fun a => Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Y.get, ofFn_eq]
  match e, he with
  | 0, _ => rw [slot_zero_cons (hm _)]
  | 1, _ => rw [slot_succ_cons (hm _), slot_zero_cons (hm _)]
  | 2, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_zero_cons (hm _)]
  | 3, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_zero_cons (hm _)]
  | 4, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _),
      slot_zero_cons (hm _)]
  | 5, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _),
      slot_succ_cons (hm _), slot_zero_cons (hm _)]
  | 6, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _),
      slot_succ_cons (hm _), slot_succ_cons (hm _), slot_zero_cons (hm _)]
  | 7, _ => rw [slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _),
      slot_succ_cons (hm _), slot_succ_cons (hm _), slot_succ_cons (hm _), slot_lt' (hm _)]

theorem cons_lt {m a r k : Nat} (ha : a < m) (hr : r < m ^ k) : a + m * r < m ^ (k + 1) :=
  calc a + m * r < m + m * r := by omega
    _ = m * (r + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ m * m ^ k := Nat.mul_le_mul_left _ hr
    _ = m ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem ofFn_lt (f : Nat → T) : Y.ofFn f < 2 ^ yw := by
  have hm : ∀ a, a % 2 ^ tw < 2 ^ tw := fun a => Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [ofFn_eq, show yw = tw * 8 from rfl, Nat.pow_mul]
  exact cons_lt (hm _) (cons_lt (hm _) (cons_lt (hm _) (cons_lt (hm _) (cons_lt (hm _) (cons_lt (hm _)
    (cons_lt (hm _) (by rw [Nat.pow_one]; exact hm _)))))))

theorem upd_lt {w n i x k : Nat} (hn : n < 2 ^ (w * k)) (hx : x < 2 ^ w) (hi : i < k) :
    upd w n i x < 2 ^ (w * k) := by
  rw [upd_parts]
  have hA := Nat.mod_lt n (Nat.two_pow_pos (w * i))
  have e : 2 ^ (w * k) = 2 ^ (w * i) * 2 ^ w * 2 ^ (w * (k - (i + 1))) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; rw [← Nat.mul_succ, ← Nat.mul_add]; congr 1; omega
  have hQ : n / (2 ^ (w * i) * 2 ^ w) < 2 ^ (w * (k - (i + 1))) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)), Nat.mul_comm, ← e]
    exact hn
  have hP := Nat.two_pow_pos (w * i)
  generalize n % 2 ^ (w * i) = A at hA ⊢
  generalize n / (2 ^ (w * i) * 2 ^ w) = Q at hQ ⊢
  rw [e]
  generalize 2 ^ (w * i) = P at hA hP ⊢
  generalize 2 ^ w = M at hx ⊢
  generalize 2 ^ (w * (k - (i + 1))) = R at hQ ⊢
  have h1 : A + P * x < P * M := by
    calc A + P * x < P + P * x := by omega
      _ = P * (x + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ P * M := Nat.mul_le_mul_left _ hx
  have h2 : P * M * Q + P * M ≤ P * M * R := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hQ
  omega

/-! ## Terms -/

theorem code_lt (k : K) : k.code < 16 := by cases k <;> decide

theorem mk_eq (k : K) (st p z t : Nat) : @Eq Nat (mk k st p z t)
    (k.code + 16 * (st % 16 + 16 * (p % 512 + 512 * (z % 4096 + 4096 * (t % 65536))))) := rfl

theorem mk_lt (k : K) (st p z t : Nat) : @LT.lt Nat instLTNat (mk k st p z t) 35184372088832 := by
  have := code_lt k
  rw [mk_eq]
  omega

theorem kind_eq (a : Nat) : T.kind a = a % 16 := rfl
theorem st_eq (a : Nat) : T.st a = a / 16 % 16 := rfl
theorem p_eq (a : Nat) : T.p a = a / 256 % 512 := rfl
theorem z_eq (a : Nat) : T.z a = a / 131072 % 4096 := rfl
theorem t_eq (a : Nat) : T.t a = a / 536870912 % 65536 := rfl

theorem mk_fields (k : K) (st p z t : Nat) :
    (mk k st p z t).kind = k.code ∧ (mk k st p z t).st = st % 16 ∧ (mk k st p z t).p = p % 512 ∧
      (mk k st p z t).z = z % 4096 ∧ (mk k st p z t).t = t % 65536 := by
  have := code_lt k
  rw [kind_eq, st_eq, p_eq, z_eq, t_eq, mk_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The halfwords of `SQRDMULH`, `0` where it is undefined. -/
def qdW (a b : BitVec 16) : BitVec 16 := (sqdmulhHLane true a b).getD 0

/-- `a` reduced to `(-q, q)`: `a - sqrdmulh(a, 10) · q`. -/
def n1W (a : BitVec 16) : BitVec 16 := a - qdW a (BitVec.ofNat 16 10) * BitVec.ofNat 16 qN

/-- `a` reduced to `[0, q)`. -/
def normW (a : BitVec 16) : BitVec 16 := n1W a + ((n1W a).sshiftRight 15 &&& BitVec.ofNat 16 qN)

/-- `b · z mod q`, as the code computes it. -/
def mmW (b : BitVec 16) (z t : Nat) : BitVec 16 :=
  b * BitVec.ofNat 16 z - qdW b (BitVec.ofNat 16 t) * BitVec.ofNat 16 qN

section
variable (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16)

/-- The value of a term. -/
def T.eval (a : T) : BitVec 16 :=
  if a.kind = 1 then L a.st a.p
  else if a.kind = 2 then O a.p
  else if a.kind = 3 then BitVec.ofNat 16 a.t
  else if a.kind = 4 then L a.st a.p * BitVec.ofNat 16 a.z
  else if a.kind = 5 then qdW (L a.st a.p) (BitVec.ofNat 16 a.t)
  else if a.kind = 6 then qdW (L a.st a.p) (BitVec.ofNat 16 a.t) * BitVec.ofNat 16 qN
  else if a.kind = 7 then mmW (L a.st a.p) a.z a.t
  else if a.kind = 8 then n1W (L a.st a.p)
  else if a.kind = 9 then (n1W (L a.st a.p)).sshiftRight 15
  else (n1W (L a.st a.p)).sshiftRight 15 &&& BitVec.ofNat 16 qN

/-- The term `a` holds of the halfword `w`: `a` is not followed (its kind is
`0` or unknown), or `w` is its value. -/
def Hd (a : T) (w : BitVec 16) : Prop := (a.kind = 0 ∨ 10 < a.kind) ∨ w = a.eval L O

/-- The coefficients after each number of layers obey the butterflies of
`R`, and `O` is the reduction of the last ones. -/
structure Model (R : Rules) : Prop where
  bfly : ∀ st p p' z t, bflyOk R st p p' z t = true →
    L (st + 1) p = L st p + mmW (L st p') z t ∧ L (st + 1) p' = L st p - mmW (L st p') z t
  out : ∀ p < 256, O p = normW (L R.layers p)

end

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem Hd.junk (w : BitVec 16) : Hd L O junkT w := .inl (.inl rfl)

theorem Hd.of_eq {a : T} {w : BitVec 16} (h : w = a.eval L O) : Hd L O a w := .inr h

theorem Hd.eq {a : T} {w : BitVec 16} (h : Hd L O a w) (hk : 1 ≤ a.kind ∧ a.kind ≤ 10) : w = a.eval L O :=
  h.resolve_left (by omega)

theorem eval_mk (k : K) (st p z t : Nat) :
    (mk k st p z t).eval L O = (match k with
      | .junk => (n1W (L (st % 16) (p % 512))).sshiftRight 15 &&& BitVec.ofNat 16 qN
      | .lv => L (st % 16) (p % 512)
      | .out => O (p % 512)
      | .c => BitVec.ofNat 16 (t % 65536)
      | .mulC => L (st % 16) (p % 512) * BitVec.ofNat 16 (z % 4096)
      | .qdC => qdW (L (st % 16) (p % 512)) (BitVec.ofNat 16 (t % 65536))
      | .mulQ => qdW (L (st % 16) (p % 512)) (BitVec.ofNat 16 (t % 65536)) * BitVec.ofNat 16 qN
      | .mm => mmW (L (st % 16) (p % 512)) (z % 4096) (t % 65536)
      | .n1 => n1W (L (st % 16) (p % 512))
      | .sraN => (n1W (L (st % 16) (p % 512))).sshiftRight 15
      | .andN => (n1W (L (st % 16) (p % 512))).sshiftRight 15 &&& BitVec.ofNat 16 qN) := by
  obtain ⟨hk, hs, hp, hz, ht⟩ := mk_fields k st p z t
  unfold T.eval
  rw [hk, hs, hp, hz, ht]
  cases k <;> rfl

theorem kind_mk (k : K) (st p z t : Nat) : (mk k st p z t).kind = k.code := (mk_fields k st p z t).1

theorem Hd.mk {k : K} (hk : k ≠ .junk) {st p z t : Nat} {w : BitVec 16} :
    Hd L O (mk k st p z t) w ↔ w = (mk k st p z t).eval L O := by
  have := code_lt k
  refine ⟨fun h => h.eq ?_, Hd.of_eq⟩
  rw [kind_mk]
  cases k <;> simp_all [K.code]

/-- Facts about a term `a` holding of `x`, by its kind. -/
theorem Hd.lv {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 1) : x = L a.st a.p := by
  rw [h.eq (by omega)]; unfold T.eval; rw [ite_eq_left hk]

theorem Hd.c {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 3) : x = BitVec.ofNat 16 a.t := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.mulC {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 4) :
    x = L a.st a.p * BitVec.ofNat 16 a.z := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.qdC {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 5) :
    x = qdW (L a.st a.p) (BitVec.ofNat 16 a.t) := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.mulQ {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 6) :
    x = qdW (L a.st a.p) (BitVec.ofNat 16 a.t) * BitVec.ofNat 16 qN := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.mm {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 7) : x = mmW (L a.st a.p) a.z a.t := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.n1 {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 8) : x = n1W (L a.st a.p) := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.sraN {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 9) :
    x = (n1W (L a.st a.p)).sshiftRight 15 := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem Hd.andN {a : T} {x : BitVec 16} (h : Hd L O a x) (hk : a.kind = 10) :
    x = (n1W (L a.st a.p)).sshiftRight 15 &&& BitVec.ofNat 16 qN := by
  rw [h.eq (by omega)]; unfold T.eval; simp [hk]

theorem st_lt (a : T) : a.st < 16 := Nat.mod_lt _ (by decide)
theorem p_lt (a : T) : a.p < 512 := Nat.mod_lt _ (by decide)
theorem z_lt (a : T) : a.z < 4096 := Nat.mod_lt _ (by decide)
theorem t_lt (a : T) : a.t < 65536 := Nat.mod_lt _ (by decide)

/-! ## The operations -/

theorem mulT_ok {a b : T} {x y : BitVec 16} (ha : Hd L O a x) (hb : Hd L O b y) : Hd L O (mulT a b) (x * y) := by
  unfold mulT
  by_cases h₁ : (Nat.beq a.kind 1 && Nat.beq b.kind 3 && Nat.blt b.t 4096) = true
  · rw [h₁, Bool.cond_true]
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h₁
    refine (Hd.mk (by decide)).2 ?_
    rw [eval_mk, ha.lv h₁.1.1, hb.c h₁.1.2, Nat.mod_eq_of_lt (st_lt a), Nat.mod_eq_of_lt (p_lt a),
      Nat.mod_eq_of_lt h₁.2]
  · rw [Bool.eq_false_iff.2 h₁, Bool.cond_false]
    by_cases h₂ : (Nat.beq a.kind 5 && Nat.beq b.kind 3 && Nat.beq b.t qN) = true
    · rw [h₂, Bool.cond_true]
      simp only [Bool.and_eq_true, Nat.beq_eq] at h₂
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, ha.qdC h₂.1.1, hb.c h₂.1.2, h₂.2, Nat.mod_eq_of_lt (st_lt a), Nat.mod_eq_of_lt (p_lt a),
        Nat.mod_eq_of_lt (t_lt a)]
    · rw [Bool.eq_false_iff.2 h₂, Bool.cond_false]; exact Hd.junk _

end

end VG.Proof.MlKem.AArch64.NttR
