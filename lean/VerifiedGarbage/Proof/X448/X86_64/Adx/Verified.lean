import VerifiedGarbage.Impl.X448.X86_64.Adx
import VerifiedGarbage.Proof.X448.X86_64.Verified
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Adx.Mul`. -/
section

/-!
# X448 on x86-64: multiplication with BMI2 and ADX

A multiply-add with both carry chains (`madd_ok`), a chain of them along a
row (`madds_ok`, by induction on the registers), a row (`rowX_ok`, for any
row of the rotating window), the rows (`rowsX_ok`, by induction on them), and
the multiplication `mulX o a b`, which ends with `reduce` (`reduce_ok`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem of_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).of = s.of := rfl
theorem of_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl

/-- `mulx hi, lo, [m]` runs as `setReg lo` then `setReg hi`. -/
theorem execMulx_mem {s : State} {hi lo : Reg} {m : MemOp} {v : BitVec 64}
    (hv : VG.X86_64.readSrc s (.mem m) = some v) :
    execMulx hi lo (.mem m) s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
  simp only [execMulx, hv, Option.map_some]

/-- `xor ebp, ebp`. -/
theorem clear_ok (s : State) :
    WP isa (.block [clear]) s fun s' =>
      s'.gpr .rbp = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rbp] s s' := by
  apply WP.of_runBlock
  simp only [clear, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, VG.X86_64.readSrc32,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self, BitVec.xor_self,
    RegUpd.cf_setReg, VG.Proof.X448.X86_64.of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial),
    (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mulx hi, lo, [m]`: `lo + 2⁶⁴ hi = rdx · v`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {m : MemOp} {v : BitVec 64}
    (hv : VG.X86_64.readSrc s (.mem m) = some v) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo (.mem m)]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X448.X86_64.execMulx_mem hv,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), RegUpd.cf_setReg, VG.Proof.X448.X86_64.of_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨mul_halves _ _, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial),
    (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adox x, r`: `x + r + OF`, the carry out in OF, CF unchanged. -/
theorem adox_ok (s : State) {x r : Reg} {o : Bool} (ho : s.of = some o) :
    WP isa (.block [.adox x (.reg r)]) s fun s' => ∃ o' : Bool, s'.of = some o' ∧ s'.cf = s.cf ∧
      (s'.gpr x).toNat + 2 ^ 64 * o'.toNat = (s.gpr x).toNat + (s.gpr r).toNat + o.toNat ∧
      Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, VG.X86_64.readSrc, ho,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, VG.Proof.X448.X86_64.of_setReg, VG.Proof.X448.X86_64.of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adcx x, r`: `x + r + CF`, the carry out in CF, OF unchanged. -/
theorem adcx_ok (s : State) {x r : Reg} {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.adcx x (.reg r)]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧ s'.of = s.of ∧
      (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + (s.gpr r).toNat + c.toNat ∧
      Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdcx, VG.X86_64.readSrc, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, VG.Proof.X448.X86_64.of_setReg, VG.Proof.X448.X86_64.of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), adc_carry _ _ _, fun r' hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `madd x y [m]`: `x + 2⁶⁴ y + o + 2⁶⁴ c + rdx · v`, the carries out in OF and
CF. -/
theorem madd_ok (s : State) {x y : Reg} {m : MemOp} {v : BitVec 64}
    (hv : VG.X86_64.readSrc s (.mem m) = some v) {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hxy : x ≠ y) (hxa : x ≠ .rax) (hxc : x ≠ .rcx) (hya : y ≠ .rax) (hyc : y ≠ .rcx) :
    WP isa (.block (madd x y (.mem m))) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧
      s'.of = some o' ∧
      (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat + 2 ^ 128 * c'.toNat =
        (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat + o.toNat + 2 ^ 64 * c.toNat +
          (s.gpr .rdx).toNat * v.toNat ∧
      Keeps [x, y, .rax, .rcx] s s' := by
  rw [madd, show ([.mulx .rcx .rax (.mem m), .adox x (.reg .rax), .adcx y (.reg .rcx)] :
    List Instr) = [.mulx .rcx .rax (.mem m)] ++ ([.adox x (.reg .rax)] ++ [.adcx y (.reg .rcx)])
    from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulx_ok s hv (by decide)) fun s1 ⟨e1, c1, o1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adox_ok s1 (o1.trans ho)) fun s2 ⟨o2, ho2, c2, e2, k2⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.adcx_ok s2 (c2.trans (c1.trans hc))) fun s3 ⟨c3, hc3, o3, e3, k3⟩ => ?_
  refine ⟨c3, o2, hc3, o3.trans ho2, ?_, ?_⟩
  · have x1 : s1.gpr x = s.gpr x := k1.1 x (by simp [hxc, hxa])
    have y2 : s2.gpr y = s.gpr y := by
      rw [k2.1 y (by simp [Ne.symm hxy]), k1.1 y (by simp [hyc, hya])]
    have a2 : s2.gpr .rcx = s1.gpr .rcx := k2.1 _ (by simp [Ne.symm hxc])
    have x3 : s3.gpr x = s2.gpr x := k3.1 x (by simp [hxy])
    have d1 : s1.gpr .rdx = s.gpr .rdx := k1.1 _ (by decide)
    rw [x1] at e2; rw [y2, a2] at e3; rw [x3]
    omega
  · exact ((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))

theorem madds_arith {B Q x1 y1 x y o c o1 c1 Y' R d V WV o' c' : Nat}
    (e1 : x1 + B * y1 + B * o1 + B * B * c1 = x + B * y + o + B * c + d * V)
    (e' : Y' + Q * o' + B * Q * c' = y1 + B * R + o1 + B * c1 + d * WV) :
    x1 + B * Y' + B * Q * o' + B * (B * Q) * c' =
      x + B * (y + B * R) + o + B * c + d * (V + B * WV) :=
  calc x1 + B * Y' + B * Q * o' + B * (B * Q) * c'
      _ = x1 + B * (Y' + Q * o' + B * Q * c') := by grind
      _ = (x1 + B * y1 + B * o1 + B * B * c1) + B * B * R + B * (d * WV) := by rw [e']; grind
      _ = _ := by rw [e1]; grind

/-- A chain of `madd`s along `x :: rs`, by the stable words `ms`: the carries
out in OF and CF, at the top register and above it. -/
theorem madds_ok (X : List Reg) (s₀ : State) (hax : Reg.rax ∈ X) (hcx : Reg.rcx ∈ X) :
    ∀ (x : Reg) (rs : List Reg) (ms : List MemOp) (vs : List (BitVec 64)) (s : State) (c o : Bool),
      Keeps X s₀ s → (∀ r ∈ x :: rs, r ∈ X) → (x :: rs).Nodup →
      (∀ r ∈ x :: rs, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx) → rs.length = ms.length →
      List.Forall₂ (fun m v => Stable X s₀ (.mem m) v) ms vs → s.cf = some c → s.of = some o →
      WP isa (.block (madds (x :: rs) (ms.map .mem))) s fun s' => ∃ c' o' : Bool,
        s'.cf = some c' ∧ s'.of = some o' ∧
        rv s' (x :: rs) + 2 ^ (64 * rs.length) * o'.toNat + 2 ^ (64 * (rs.length + 1)) * c'.toNat =
          rv s (x :: rs) + o.toNat + 2 ^ 64 * c.toNat + (s.gpr .rdx).toNat * wv vs ∧
        Keeps (.rax :: .rcx :: x :: rs) s s'
  | x, [], ms, vs, s, c, o, _, _, _, _, hl, hf, hc, ho => by
    cases ms with
    | nil =>
      cases hf
      refine WP.block_nil ⟨c, o, hc, ho, ?_, Keeps.refl _ _⟩
      simp only [wv, List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add,
        Nat.mul_one]
      omega
    | cons => simp at hl
  | _, _ :: _, [], _, _, _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | x, y :: rs, m :: ms, vs, s, c, o, hk, hX, hnd, hr, hl, hf, hc, ho => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hxr := hr x List.mem_cons_self
    have hyr := hr y (List.mem_cons_of_mem _ List.mem_cons_self)
    have hxy : x ≠ y := fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.mem_cons_self)
    have hxn : x ∉ y :: rs := (List.nodup_cons.mp hnd).1
    have hv' : VG.X86_64.readSrc s (.mem m) = some v := hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    rw [List.map_cons, madds, WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.X86_64.madd_ok s hv' hc ho hxy hxr.1 hxr.2.1 hyr.1 hyr.2.1)
      fun s1 ⟨c1, o1, hc1, ho1, e1, k1⟩ => ?_
    have hk1 : Keeps X s₀ s1 := hk.trans (k1.mono fun r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact hX _ List.mem_cons_self
      · exact hX _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact hax
      · exact hcx)
    refine WP.mono (VG.Proof.X448.X86_64.madds_ok X s₀ hax hcx y rs ms vs s1 c1 o1 hk1
      (fun r h => hX r (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2
      (fun r h => hr r (List.mem_cons_of_mem _ h)) (by simpa using hl) hf hc1 ho1)
      fun s' ⟨c', o', hc', ho', e', k'⟩ => ⟨c', o', hc', ho', ?_, ?_⟩
    · have x' : s'.gpr x = s1.gpr x := k'.1 x (by
        simp only [List.mem_cons, not_or] at hxn ⊢
        exact ⟨hxr.1, hxr.2.1, hxn⟩)
      have d1 : s1.gpr .rdx = s.gpr .rdx := k1.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => hxr.2.2 e.symm, fun e => hyr.2.2 e.symm, by decide, by decide⟩)
      have r1 : rv s1 rs = rv s rs := rv_congr fun r h => k1.1 r (by
        have hrr := hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => hxn (e ▸ List.mem_cons_of_mem _ h), fun e => ?_, hrr.1, hrr.2.1⟩
        exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (e ▸ h))
      rw [d1] at e'
      simp only [rv] at e'
      rw [r1] at e'
      simp only [rv, List.length_cons, wv] at e1 e' ⊢
      rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide] at e1
      rw [pow64_succ rs.length] at e'
      rw [x', pow64_succ (rs.length + 1), pow64_succ rs.length]
      exact VG.Proof.X448.X86_64.madds_arith (B := 2 ^ 64) (Q := 2 ^ (64 * rs.length)) e1 e'
    · refine ⟨fun r hr' => ?_, k'.2.1.trans k1.2.1, k'.2.2.1.trans k1.2.2.1, k'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [k'.1 r (by simp only [List.mem_cons, not_or]; exact ⟨hr'.1, hr'.2.1, hr'.2.2.2⟩),
        k1.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                   exact ⟨hr'.2.2.1, hr'.2.2.2.1, hr'.1, hr'.2.1⟩)]

/-! ## The rotating window -/

theorem win_mod (i k : Nat) : win i k = win (i % 8) k := by
  unfold win; rw [show (i + k) % 8 = (i % 8 + k) % 8 by omega]

theorem wins_mod (i n : Nat) : wins i n = wins (i % 8) n := by
  unfold wins; rw [show win i = win (i % 8) from funext (VG.Proof.X448.X86_64.win_mod i)]

theorem wins_length (i n : Nat) : (wins i n).length = n := by simp [wins]

theorem wins_succ (i : Nat) : wins i 8 = win i 0 :: wins (i + 1) 7 := by
  unfold wins
  rw [show (8 : Nat) = 7 + 1 from rfl, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg (win i 0 :: ·) (congrArg (List.map · _) (funext fun k => ?_))
  show win i (k + 1) = win (i + 1) k
  unfold win; rw [show i + (k + 1) = i + 1 + k by omega]

theorem wins_snoc (i : Nat) : wins i 8 = wins i 7 ++ [win i 7] := by
  unfold wins; rw [show (8 : Nat) = 7 + 1 from rfl, List.range_succ, List.map_append]; rfl

theorem win_facts : ∀ i < 8, (wins i 8).Nodup ∧ win i 7 ∉ wins i 7 ∧
    ∀ r ∈ wins i 8, r ∈ clob ∧ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by decide

theorem wins_facts (i : Nat) : (wins i 8).Nodup ∧ win i 7 ∉ wins i 7 ∧
    ∀ r ∈ wins i 8, r ∈ clob ∧ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by
  rw [VG.Proof.X448.X86_64.wins_mod i 8, VG.Proof.X448.X86_64.wins_mod i 7, VG.Proof.X448.X86_64.win_mod i 7]; exact VG.Proof.X448.X86_64.win_facts _ (Nat.mod_lt _ (by decide))

theorem win_mem (i k : Nat) (hk : k < 8) : win i k ∈ wins i 8 :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem wins7_sub (i : Nat) {r : Reg} (h : r ∈ wins i 7) : r ∈ wins i 8 := by
  rw [VG.Proof.X448.X86_64.wins_snoc]; exact List.mem_append_left _ h

theorem wins_succ_sub (i : Nat) {r : Reg} (h : r ∈ wins (i + 1) 7) : r ∈ wins i 8 := by
  rw [VG.Proof.X448.X86_64.wins_succ]; exact List.mem_cons_of_mem _ h

theorem rv_append (s : State) : ∀ xs ys : List Reg,
    rv s (xs ++ ys) = rv s xs + 2 ^ (64 * xs.length) * rv s ys
  | [], ys => by simp [rv]
  | x :: xs, ys => by
    rw [List.cons_append, rv, rv, VG.Proof.X448.X86_64.rv_append s xs ys, List.length_cons, pow64_succ]
    generalize 2 ^ (64 * xs.length) = Q
    grind

theorem stable_scs_mem {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (fun m v => Stable X s (.mem m) v) (ds.map sc) (ds.map fun d => word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (stable_sc hs hX (h d List.mem_cons_self))
      (VG.Proof.X448.X86_64.stable_scs_mem hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-! ## A row -/

theorem row_arith {Q B L4 w4 w5 o4 c4 o5 R0 dA : Nat} (hb : R0 + dA < B * Q)
    (c4l : c4 ≤ 1) (o5l : o5 ≤ 1)
    (e4 : L4 + Q * w4 + Q * o4 + B * Q * c4 = R0 + dA) (e5 : w5 + B * o5 = w4 + o4) :
    L4 + Q * w5 = R0 + dA := by
  have e : L4 + Q * w5 + B * Q * o5 + B * Q * c4 = R0 + dA := by
    have := congrArg (Q * ·) e5
    simp only [Nat.mul_add] at this
    rw [show B * Q * o5 = Q * (B * o5) by grind]
    generalize Q * w5 = a1 at *; generalize Q * (B * o5) = a2 at *
    generalize Q * w4 = a3 at *; generalize Q * o4 = a4 at *; generalize B * Q * c4 = a5 at *
    omega
  generalize B * Q = BQ at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp o5l with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c4l with rfl | rfl <;> omega

theorem row_bound {R0 d A B Q : Nat} (hR : R0 < Q) (hd : d < B) (hA : A < Q) :
    R0 + d * A < B * Q := by
  have h1 : d * A ≤ (B - 1) * Q := Nat.mul_le_mul (by omega) (Nat.le_of_lt hA)
  have h2 : (B - 1) * Q + Q = B * Q := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  omega

theorem rowX_eq (a b i : Nat) : rowX a b i = loads (b + 8 * i) ([.rdx] : List Reg) ++
    (([.mov32 (win i 7) (.imm 0), clear] : List Instr) ++
    (madds (win i 0 :: wins (i + 1) 7)
      ((([a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] : List Nat).map sc).map .mem) ++
    (([.adox (win i 7) (.reg .rbp)] : List Instr) ++ stores (h i) [win i 0]))) := by
  rw [rowX, ← VG.Proof.X448.X86_64.wins_succ]; rfl

/-- Row `i`: the window plus `b_i · [a]`, whose lowest word is stored at
`h i`. -/
theorem rowX_ok {t : State} {base : Addr} (hs : Scr t base) {a b i : Nat} (ha : Slot a)
    (hb : Slot b) (hi : i < 7) :
    WP isa (.block (rowX a b i)) t fun t' =>
      (word t'.mem base (h i)).toNat + 2 ^ 64 * rv t' (wins (i + 1) 7) =
        rv t (wins i 7) + (word t.mem base (b + 8 * i)).toNat * fe t.mem base a ∧
      KeepsR clob t t' ∧ Outside base (h i) 8 t.mem t'.mem := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  obtain ⟨nd, h7, hr⟩ := VG.Proof.X448.X86_64.wins_facts i
  have r7 := hr _ (VG.Proof.X448.X86_64.win_mem i 7 (by decide))
  rw [VG.Proof.X448.X86_64.rowX_eq, WP.block_append_iff]
  refine WP.mono (loads_ok hs (b + 8 * i) [.rdx] (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)) fun s1 ⟨g1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have d1 : s1.gpr .rdx = word t.mem base (b + 8 * i) := by
    have := g1 0 (by decide) .r8; simpa using this
  rw [WP.block_append_iff, show ([.mov32 (win i 7) (.imm 0), clear] : List Instr) =
    [.mov32 (win i 7) (.imm 0)] ++ [clear] from rfl, WP.block_append_iff]
  refine WP.mono (mov32_ok s1 (win i 7) 0) fun s2 ⟨z2, k2⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.clear_ok s2) fun s3 ⟨p3, c3, o3, k3⟩ => ?_
  have hrdi7 : Reg.rdi ∉ [win i 7] := by simpa using Ne.symm r7.2.2.2.2.2
  have hs3 := (hs1.of_keeps k2 hrdi7).of_keeps k3 (by decide)
  have m3 : s3.mem = t.mem := k3.2.1.trans (k2.2.1.trans k1.2.1)
  rw [WP.block_append_iff]
  have hsrc := VG.Proof.X448.X86_64.stable_scs_mem (X := clob) hs3 (by decide)
    [a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  refine WP.mono (VG.Proof.X448.X86_64.madds_ok clob s3 (by decide) (by decide) (win i 0) (wins (i + 1) 7) _ _ s3 false
    false (Keeps.refl _ _) (fun r h => (hr r (by rw [VG.Proof.X448.X86_64.wins_succ]; exact h)).1)
    (by rw [← VG.Proof.X448.X86_64.wins_succ]; exact nd) (fun r h => by
      have := hr r (by rw [VG.Proof.X448.X86_64.wins_succ]; exact h); exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩)
    (by rw [VG.Proof.X448.X86_64.wins_length]; rfl) hsrc c3 o3) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adox_ok s4 ho4) fun s5 ⟨o5, _, _, e5, k5⟩ => ?_
  have hs5 := (hs3.of_keeps k4 (by
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, by decide, Ne.symm (hr _ (VG.Proof.X448.X86_64.win_mem i 0 (by decide))).2.2.2.2.2,
      fun e => (hr _ (VG.Proof.X448.X86_64.wins_succ_sub i e)).2.2.2.2.2 rfl⟩)).of_keeps k5 hrdi7
  refine WP.mono (stores_ok hs5 (h i) [win i 0] (by simp only [h, ACC]; simp; omega))
    fun s6 ⟨m6, out6, g6, rd6, wr6⟩ => ⟨?_, ?_, ?_⟩
  · -- the arithmetic
    have w6 : (word s6.mem base (h i)).toNat = (s5.gpr (win i 0)).toNat := by
      simpa [mv, rv] using m6
    have v6 : rv s6 (wins (i + 1) 7) = rv s5 (wins (i + 1) 7) := rv_congr fun r _ => g6 r
    have L : (s5.gpr (win i 0)).toNat + 2 ^ 64 * rv s5 (wins (i + 1) 7) = rv s5 (wins i 8) := by
      rw [VG.Proof.X448.X86_64.wins_succ]; rfl
    rw [w6, v6, L, VG.Proof.X448.X86_64.wins_snoc, VG.Proof.X448.X86_64.rv_append, VG.Proof.X448.X86_64.wins_length]
    have v5 : rv s5 (wins i 7) = rv s4 (wins i 7) := rv_congr fun r hr' => k5.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun e => h7 (e ▸ hr'))
    have p4 : s4.gpr .rbp = 0 := by
      rw [k4.1 _ (by
        simp only [List.mem_cons, not_or]
        refine ⟨by decide, by decide, fun e => (hr _ (VG.Proof.X448.X86_64.win_mem i 0 (by decide))).2.2.2.2.1 e.symm,
          fun e => ?_⟩
        exact (hr _ (VG.Proof.X448.X86_64.wins_succ_sub i e)).2.2.2.2.1 rfl), p3]
    rw [← VG.Proof.X448.X86_64.wins_succ, VG.Proof.X448.X86_64.wins_snoc] at e4
    simp only [VG.Proof.X448.X86_64.rv_append, VG.Proof.X448.X86_64.wins_length] at e4
    rw [p4] at e5
    have v3 : rv s3 (wins i 7) = rv t (wins i 7) := rv_congr fun r hr' => by
      have := hr r (VG.Proof.X448.X86_64.wins7_sub i hr')
      rw [k3.1 r (by simp [this.2.2.2.2.1]), k2.1 r (by simp; exact fun e => h7 (e ▸ hr')),
        k1.1 r (by simp [this.2.2.2.1])]
    have z3 : s3.gpr (win i 7) = 0 := by rw [k3.1 _ (by simp [r7.2.2.2.2.1]), z2]; rfl
    have d3 : s3.gpr .rdx = s1.gpr .rdx := by
      rw [k3.1 _ (by decide), k2.1 _ (by simp [r7.2.2.2.1.symm])]
    have A3 : wv (([a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48] : List Nat).map
        fun d => word s3.mem base d) = fe t.mem base a := by rw [m3]; exact wv_words' _ _ _
    have hb := VG.Proof.X448.X86_64.row_bound (Q := 2 ^ (64 * 7)) (B := 2 ^ 64)
      (Nat.lt_of_lt_of_eq (rv_lt t (wins i 7)) (by rw [VG.Proof.X448.X86_64.wins_length]))
      (word t.mem base (b + 8 * i)).isLt (mv_lt t.mem base a 7)
    rw [pow64_succ 7] at e4
    rw [v5]
    generalize 2 ^ (64 * 7) = Q at e4 hb ⊢
    simp only [rv, z3, d3, d1, A3, v3, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      toNat_zero64] at e4 e5 ⊢
    exact VG.Proof.X448.X86_64.row_arith hb (Bool.toNat_le _) (Bool.toNat_le _) e4 e5
  · refine ⟨fun r hr' => ?_, ?_, ?_⟩
    · have nw : r ∉ wins i 8 := fun h => hr' (hr r h).1
      rw [g6, k5.1 r (by simp; exact fun e => nw (e ▸ VG.Proof.X448.X86_64.win_mem i 7 (by decide))),
        k4.1 r (by
          simp only [List.mem_cons, not_or]
          refine ⟨fun e => hr' (e ▸ by decide), fun e => hr' (e ▸ by decide),
            fun e => nw (e ▸ VG.Proof.X448.X86_64.win_mem i 0 (by decide)), fun e => nw (VG.Proof.X448.X86_64.wins_succ_sub i e)⟩),
        k3.1 r (by simp; exact fun e => hr' (e ▸ by decide)),
        k2.1 r (by simp; exact fun e => nw (e ▸ VG.Proof.X448.X86_64.win_mem i 7 (by decide))),
        k1.1 r (by simp; exact fun e => hr' (e ▸ by decide))]
    · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
    · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [← k5.2.1.trans (k4.2.1.trans m3)]; exact out6

/-! ## The product -/

theorem zeros_ok : ∀ (rs : List Reg) (s : State),
    WP isa (.block (rs.map fun r => .mov32 r (.imm 0))) s fun s' =>
      (∀ r ∈ rs, s'.gpr r = 0) ∧ Keeps rs s s'
  | [], s => WP.block_nil ⟨by simp, Keeps.refl _ _⟩
  | r :: rs, s => by
    rw [List.map_cons, show ∀ (x : Instr) l, x :: l = [x] ++ l from fun _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (mov32_ok s r 0) fun s1 ⟨z1, k1⟩ =>
      WP.mono (VG.Proof.X448.X86_64.zeros_ok rs s1) fun s' ⟨z', k'⟩ => ⟨fun r' hr' => ?_, ?_⟩
    · by_cases h : r' ∈ rs
      · exact z' r' h
      · have : r' = r := by simpa [h] using hr'
        subst this; rw [k'.1 _ h, z1]; rfl
    · exact (k1.mono fun _ h => by simp_all).trans (k'.mono fun _ h => List.mem_cons_of_mem _ h)

theorem rv_zero (s : State) : ∀ rs : List Reg, (∀ r ∈ rs, s.gpr r = 0) → rv s rs = 0
  | [], _ => rfl
  | r :: rs, h => by
    rw [rv, h r List.mem_cons_self, VG.Proof.X448.X86_64.rv_zero s rs fun r' h' => h r' (List.mem_cons_of_mem _ h')]; rfl

theorem rows_arith {M P B W' R' R bn A MB : Nat} (tv : M + P * R = MB * A)
    (e : W' + B * R' = R + bn * A) : M + P * W' + B * P * R' = (MB + P * bn) * A :=
  calc M + P * W' + B * P * R'
      _ = M + P * (W' + B * R') := by grind
      _ = (M + P * R) + P * bn * A := by rw [e]; grind
      _ = _ := by rw [tv]; grind

/-- The rows: `[ACC]` and the last window are `[b] · [a]`. -/
theorem rowsX_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) (hz : rv s (wins 0 7) = 0) :
    WP isa (.block ((List.range 7).flatMap (rowX a b))) s fun t =>
      KeepsR clob s t ∧ Outside base ACC 56 s.mem t.mem ∧
      mv t.mem base ACC 7 + 2 ^ (64 * 7) * rv t (wins 7 7) = fe s.mem base b * fe s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  let inv := fun n (t : State) => KeepsR clob s t ∧ Outside base ACC (8 * n) s.mem t.mem ∧
    mv t.mem base ACC n + 2 ^ (64 * n) * rv t (wins n 7) = mv s.mem base b n * fe s.mem base a
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block (rowX a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tout, tv⟩
    have ht : Scr t base := hs.of_keepsR tk (by decide)
    refine WP.mono (VG.Proof.X448.X86_64.rowX_ok ht ha hb hn) fun t' ⟨e, k', out'⟩ => ⟨tk.trans k', ?_, ?_⟩
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        (out'.mono (by simp only [h]; omega) (by simp only [h]; omega))
    · have m1 : mv t'.mem base ACC n = mv t.mem base ACC n :=
        out'.mv (Or.inl (by simp only [h]; omega)) (by simp only [ACC]; omega)
      have w1 : mv t'.mem base (ACC + 8 * n) 1 = (word t'.mem base (h n)).toNat := by
        simp only [mv, h, Nat.mul_zero, Nat.add_zero]
      have b1 : word t.mem base (b + 8 * n) = word s.mem base (b + 8 * n) :=
        tout.word (Or.inl (by simp only [ACC]; omega)) (by omega)
      have a1 : fe t.mem base a = fe s.mem base a :=
        tout.fe (Or.inl (by simp only [ACC]; omega)) (by omega)
      have mb : mv s.mem base b (n + 1) =
          mv s.mem base b n + 2 ^ (64 * n) * (word s.mem base (b + 8 * n)).toNat := by
        rw [mv_add]; simp only [mv, Nat.mul_zero, Nat.add_zero]
      rw [mv_add, m1, w1, mb, pow64_succ]
      rw [b1, a1] at e
      exact VG.Proof.X448.X86_64.rows_arith (B := 2 ^ 64) tv e
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by simp [mv, hz]⟩)
    fun t ⟨tk, tout, tv⟩ => ⟨tk, tout, tv⟩

theorem wins07_clob : ∀ r ∈ wins 0 7, r ∈ clob := by decide

/-- `[o] = [a] · [b]`, by rows. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  simp only [mulX, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.zeros_ok (wins 0 7) s) fun s1 ⟨z1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.rowsX_ok hs1 ha hb (VG.Proof.X448.X86_64.rv_zero s1 _ z1)) fun s2 ⟨k2, out2, v2⟩ => ?_
  have hs2 := hs1.of_keepsR k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs2 (h 7) (wins 7 7) (by rw [VG.Proof.X448.X86_64.wins_length]; decide))
    fun s3 ⟨m3, out3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  refine WP.mono (reduce_ok hs3 ho) fun s4 ⟨e4, g4, rd4, wr4, out4⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    rw [g4 r hr, g3 r, k2.1 r hr, k1.1 r fun h => hr (VG.Proof.X448.X86_64.wins07_clob r h)]
  · rw [rd4, rd3, k2.2.1, k1.2.2.1]
  · rw [wr4, wr3, k2.2.2, k1.2.2.2]
  · rw [← k1.2.1]
    have ho' : o + 56 ≤ ACC := ho
    exact ((out2.mono (Nat.le_refl _) (by omega)).right o 56).trans
      (((out3.mono (by simp only [h]; omega) (by rw [VG.Proof.X448.X86_64.wins_length]; simp only [h]; omega)).right
        o 56).trans (out4.left ACC 112))
  · have m1 : s1.mem = s.mem := k1.2.1
    have hm : mv s3.mem base ACC 7 = mv s2.mem base ACC 7 :=
      out3.mv (Or.inl (by simp only [h]; omega)) (by simp only [ACC]; omega)
    rw [VG.Proof.X448.X86_64.wins_length] at m3
    rw [show ACC + 56 = h 7 from rfl, m3, hm, show (448 : Nat) = 64 * 7 from rfl, v2, m1] at e4
    rw [Nat.mul_comm] at e4
    exact toFe_mul e4

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr`. -/
section

/-!
# X448 on x86-64: squaring with BMI2 and ADX

The rows of cross products (`sqRow_ok`, for any row: the window shrinks by
one word a row), the doubling and the squares (`dblRow_ok`, two words a
step, the carries in CF and OF), and `sqrX`, which ends with `reduce`.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem wins_cons (i n : Nat) : wins i (n + 1) = win i 0 :: wins (i + 1) n := by
  unfold wins
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg (win i 0 :: ·) (congrArg (List.map · _) (funext fun k => ?_))
  show win i (k + 1) = win (i + 1) k
  unfold win; rw [show i + (k + 1) = i + 1 + k by omega]

theorem wins_sub {i n : Nat} (hn : n ≤ 8) {r : Reg} (h : r ∈ wins i n) : r ∈ wins i 8 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  exact VG.Proof.X448.X86_64.win_mem i k (by have := List.mem_range.mp hk; omega)

theorem wins_nodup {i n : Nat} (hn : n ≤ 8) : (wins i n).Nodup :=
  (VG.Proof.X448.X86_64.wins_facts i).1.sublist ((List.range_sublist.mpr hn).map _)

theorem wv_range (m : Mem) (base : Addr) :
    ∀ n d, wv ((List.range n).map fun j => word m base (d + 8 * j)) = mv m base d n
  | 0, _ => rfl
  | n + 1, d => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, wv, mv, Nat.mul_zero, Nat.add_zero,
      ← VG.Proof.X448.X86_64.wv_range m base n (d + 8)]
    refine congrArg (fun x => _ + 2 ^ 64 * wv x) (congrArg (List.map · _) (funext fun j => ?_))
    show word m base (d + 8 * (j + 1)) = word m base (d + 8 + 8 * j)
    rw [show d + 8 * (j + 1) = d + 8 + 8 * j by omega]

theorem stable_range {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ n d, d + 8 * n ≤ 8192 →
      List.Forall₂ (fun m v => Stable X s (.mem m) v) ((List.range n).map fun j => sc (d + 8 * j))
        ((List.range n).map fun j => word s.mem base (d + 8 * j))
  | 0, _, _ => .nil
  | n + 1, d, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    refine .cons (by rw [Nat.mul_zero, Nat.add_zero]; exact stable_sc hs hX (by omega)) ?_
    have := VG.Proof.X448.X86_64.stable_range hs hX n (d + 8) (by omega)
    rwa [show ((fun j => sc (d + 8 + 8 * j)) : Nat → MemOp) =
        (fun j => sc (d + 8 * j)) ∘ Nat.succ from funext fun j => by
          show sc (d + 8 + 8 * j) = sc (d + 8 * (j + 1))
          rw [show d + 8 * (j + 1) = d + 8 + 8 * j by omega],
      show ((fun j => word s.mem base (d + 8 + 8 * j)) : Nat → BitVec 64) =
        (fun j => word s.mem base (d + 8 * j)) ∘ Nat.succ from funext fun j => by
          show word s.mem base (d + 8 + 8 * j) = word s.mem base (d + 8 * (j + 1))
          rw [show d + 8 * (j + 1) = d + 8 + 8 * j by omega]] at this

theorem wins_snoc' (i n : Nat) : wins i (n + 1) = wins i n ++ [win i n] := by
  unfold wins; rw [List.range_succ, List.map_append]; rfl

theorem win_succ (i : Nat) : win (i + 1) 0 = win i 1 := rfl

/-! ## The cross products -/

theorem sqRow_eq (a i : Nat) (hi : i ≤ 5) : sqRow a i = loads (a + 8 * i) ([.rdx] : List Reg) ++
    (([.mov32 (win (2 * i + 1) (6 - i)) (.imm 0), clear] : List Instr) ++
    (madds (win (2 * i + 1) 0 :: wins (2 * i + 1 + 1) (6 - i))
      (((List.range (6 - i)).map fun j => sc (a + 8 * (i + 1) + 8 * j)).map .mem) ++
    (([.adox (win (2 * i + 1) (6 - i)) (.reg .rbp)] : List Instr) ++
    (stores (h (2 * i + 1)) [win (2 * i + 1) 0] ++ stores (h (2 * i + 2)) [win (2 * i + 1) 1])))) := by
  rw [sqRow, show 7 - i = 6 - i + 1 by omega, VG.Proof.X448.X86_64.wins_cons, List.map_map]; rfl

/-- Row `i` of the cross products: the window `2i + 1, …, i + 6` plus
`a_i · (a_{i+1}, …, a_6)`, whose two lowest words are stored. -/
theorem sqRow_ok {t : State} {base : Addr} (hs : Scr t base) {a i : Nat} (ha : Slot a)
    (hi : i ≤ 5) :
    WP isa (.block (sqRow a i)) t fun t' =>
      (word t'.mem base (h (2 * i + 1))).toNat + 2 ^ 64 * ((word t'.mem base (h (2 * i + 2))).toNat +
        2 ^ 64 * rv t' (wins (2 * i + 3) (5 - i))) =
        rv t (wins (2 * i + 1) (6 - i)) +
          (word t.mem base (a + 8 * i)).toNat * mv t.mem base (a + 8 * (i + 1)) (6 - i) ∧
      KeepsR clob t t' ∧ Outside base (h (2 * i + 1)) 16 t.mem t'.mem := by
  have ha' : a + 56 ≤ 1536 := ha
  obtain ⟨_, _, hr⟩ := VG.Proof.X448.X86_64.wins_facts (2 * i + 1)
  have hm8 : 6 - i + 1 ≤ 8 := by omega
  have r7 := hr _ (VG.Proof.X448.X86_64.win_mem (2 * i + 1) (6 - i) (by omega))
  have hL : win (2 * i + 1) 0 :: wins (2 * i + 1 + 1) (6 - i) = wins (2 * i + 1) (6 - i + 1) :=
    (VG.Proof.X448.X86_64.wins_cons _ _).symm
  have hrL : ∀ r ∈ wins (2 * i + 1) (6 - i + 1), r ∈ clob ∧ r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧
      r ≠ .rbp ∧ r ≠ .rdi := fun r h => hr r (VG.Proof.X448.X86_64.wins_sub hm8 h)
  have top_nm : win (2 * i + 1) (6 - i) ∉ wins (2 * i + 1) (6 - i) := by
    have := VG.Proof.X448.X86_64.wins_nodup (i := 2 * i + 1) hm8
    rw [VG.Proof.X448.X86_64.wins_snoc'] at this
    exact fun h => (List.nodup_append.mp this).2.2 _ h _ List.mem_cons_self rfl
  rw [VG.Proof.X448.X86_64.sqRow_eq a i hi, WP.block_append_iff]
  refine WP.mono (loads_ok hs (a + 8 * i) [.rdx] (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)) fun s1 ⟨g1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have d1 : s1.gpr .rdx = word t.mem base (a + 8 * i) := by
    have := g1 0 (by decide) .r8; simpa using this
  rw [WP.block_append_iff, show ([.mov32 (win (2 * i + 1) (6 - i)) (.imm 0), clear] : List Instr) =
    [.mov32 (win (2 * i + 1) (6 - i)) (.imm 0)] ++ [clear] from rfl, WP.block_append_iff]
  refine WP.mono (mov32_ok s1 _ 0) fun s2 ⟨z2, k2⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.clear_ok s2) fun s3 ⟨p3, c3, o3, k3⟩ => ?_
  have hrdi7 : Reg.rdi ∉ [win (2 * i + 1) (6 - i)] := by simpa using Ne.symm r7.2.2.2.2.2
  have hs3 := (hs1.of_keeps k2 hrdi7).of_keeps k3 (by decide)
  have m3 : s3.mem = t.mem := k3.2.1.trans (k2.2.1.trans k1.2.1)
  rw [WP.block_append_iff]
  have hsrc := VG.Proof.X448.X86_64.stable_range (X := clob) hs3 (by decide) (6 - i) (a + 8 * (i + 1)) (by omega)
  refine WP.mono (VG.Proof.X448.X86_64.madds_ok clob s3 (by decide) (by decide) _ _ _ _ s3 false false (Keeps.refl _ _)
    (fun r h => (hrL r (by rw [← hL]; exact h)).1) (by rw [hL]; exact VG.Proof.X448.X86_64.wins_nodup hm8)
    (fun r h => by
      have := hrL r (by rw [← hL]; exact h); exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩)
    (by rw [VG.Proof.X448.X86_64.wins_length, List.length_map, List.length_range]) hsrc c3 o3)
    fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [hL] at e4 k4
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adox_ok s4 ho4) fun s5 ⟨o5, _, _, e5, k5⟩ => ?_
  have hs5 := (hs3.of_keeps k4 (by
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, by decide, fun e => (hrL _ e).2.2.2.2.2 rfl⟩)).of_keeps k5 hrdi7
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs5 (h (2 * i + 1)) [win (2 * i + 1) 0]
    (by simp only [h, ACC, List.length_cons, List.length_nil]; omega))
    fun s6 ⟨m6, out6, g6, rd6, wr6⟩ => ?_
  have hs6 : Scr s6 base := ⟨(g6 _).trans hs5.rdi, wr6 ▸ hs5.wr, hs5.nowrap⟩
  refine WP.mono (stores_ok hs6 (h (2 * i + 2)) [win (2 * i + 1) 1]
    (by simp only [h, ACC, List.length_cons, List.length_nil]; omega))
    fun s7 ⟨m7, out7, g7, rd7, wr7⟩ => ⟨?_, ?_, ?_⟩
  · have w7a : (word s7.mem base (h (2 * i + 1))).toNat = (s5.gpr (win (2 * i + 1) 0)).toNat := by
      rw [out7.word (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega)]
      simpa [mv, rv] using m6
    have w7b : (word s7.mem base (h (2 * i + 2))).toNat = (s5.gpr (win (2 * i + 1) 1)).toNat := by
      have := m7; simp only [mv, rv, List.length_cons, List.length_nil, Nat.mul_zero,
        Nat.add_zero] at this; rw [this, g6]
    have v7 : rv s7 (wins (2 * i + 3) (5 - i)) = rv s5 (wins (2 * i + 3) (5 - i)) :=
      rv_congr fun r _ => (g7 r).trans (g6 r)
    have L5 : (s5.gpr (win (2 * i + 1) 0)).toNat + 2 ^ 64 * ((s5.gpr (win (2 * i + 1) 1)).toNat +
        2 ^ 64 * rv s5 (wins (2 * i + 3) (5 - i))) = rv s5 (wins (2 * i + 1) (6 - i + 1)) := by
      rw [VG.Proof.X448.X86_64.wins_cons, show 6 - i = 5 - i + 1 by omega, VG.Proof.X448.X86_64.wins_cons, VG.Proof.X448.X86_64.win_succ]; rfl
    rw [w7a, w7b, v7, L5, VG.Proof.X448.X86_64.wins_snoc', VG.Proof.X448.X86_64.rv_append, VG.Proof.X448.X86_64.wins_length]
    have v5 : rv s5 (wins (2 * i + 1) (6 - i)) = rv s4 (wins (2 * i + 1) (6 - i)) :=
      rv_congr fun r hr' => k5.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun e => top_nm (e ▸ hr'))
    have p4 : s4.gpr .rbp = 0 := by
      rw [k4.1 _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨by decide, by decide, fun e => (hrL _ e).2.2.2.2.1 rfl⟩), p3]
    rw [VG.Proof.X448.X86_64.wins_snoc'] at e4
    simp only [VG.Proof.X448.X86_64.rv_append, VG.Proof.X448.X86_64.wins_length] at e4
    rw [p4] at e5
    have v3 : rv s3 (wins (2 * i + 1) (6 - i)) = rv t (wins (2 * i + 1) (6 - i)) :=
      rv_congr fun r hr' => by
        have := hrL r (by rw [VG.Proof.X448.X86_64.wins_snoc']; exact List.mem_append_left _ hr')
        rw [k3.1 r (by simp [this.2.2.2.2.1]), k2.1 r (by simp; exact fun e => top_nm (e ▸ hr')),
          k1.1 r (by simp [this.2.2.2.1])]
    have z3 : s3.gpr (win (2 * i + 1) (6 - i)) = 0 := by
      rw [k3.1 _ (by simp [r7.2.2.2.2.1]), z2]; rfl
    have d3 : s3.gpr .rdx = s1.gpr .rdx := by
      rw [k3.1 _ (by decide), k2.1 _ (by simp [r7.2.2.2.1.symm])]
    have A3 : wv ((List.range (6 - i)).map fun j => word s3.mem base (a + 8 * (i + 1) + 8 * j)) =
        mv t.mem base (a + 8 * (i + 1)) (6 - i) := by rw [m3]; exact VG.Proof.X448.X86_64.wv_range _ _ _ _
    have hb := VG.Proof.X448.X86_64.row_bound (Q := 2 ^ (64 * (6 - i))) (B := 2 ^ 64)
      (Nat.lt_of_lt_of_eq (rv_lt t (wins (2 * i + 1) (6 - i))) (by rw [VG.Proof.X448.X86_64.wins_length]))
      (word t.mem base (a + 8 * i)).isLt (mv_lt t.mem base (a + 8 * (i + 1)) (6 - i))
    rw [pow64_succ (6 - i)] at e4
    rw [v5]
    generalize 2 ^ (64 * (6 - i)) = Q at e4 hb ⊢
    simp only [rv, z3, d3, d1, A3, v3, Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
      toNat_zero64] at e4 e5 ⊢
    exact VG.Proof.X448.X86_64.row_arith hb (Bool.toNat_le _) (Bool.toNat_le _) e4 e5
  · have nw : ∀ r, r ∉ clob → r ∉ wins (2 * i + 1) (6 - i + 1) := fun r hr' h => hr' (hrL r h).1
    refine ⟨fun r hr' => ?_, ?_, ?_⟩
    · rw [g7, g6, k5.1 r (by simp; exact fun e => nw r hr' (e ▸ by
          rw [VG.Proof.X448.X86_64.wins_snoc']; exact List.mem_append_right _ List.mem_cons_self)),
        k4.1 r (by
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => hr' (e ▸ by decide), fun e => hr' (e ▸ by decide), nw r hr'⟩),
        k3.1 r (by simp; exact fun e => hr' (e ▸ by decide)),
        k2.1 r (by simp; exact fun e => nw r hr' (e ▸ by
          rw [VG.Proof.X448.X86_64.wins_snoc']; exact List.mem_append_right _ List.mem_cons_self)),
        k1.1 r (by simp; exact fun e => hr' (e ▸ by decide))]
    · rw [rd7, rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
    · rw [wr7, wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [← k5.2.1.trans (k4.2.1.trans m3)]
    exact (out6.mono (Nat.le_refl _) (by simp only [List.length_cons, List.length_nil]; omega)).trans
      (out7.mono (by simp only [h]; omega)
        (by simp only [h, List.length_cons, List.length_nil]; omega))

/-! ## A square by rows -/

/-- The cross products of the `n` words at `d`, by rows: `a_0 · (a_1, …)`, then
the rest two words up. -/
def crossR (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | d, n + 1 => (word m base d).toNat * mv m base (d + 8) n + 2 ^ 64 * 2 ^ 64 * VG.Proof.X448.X86_64.crossR m base (d + 8) n

/-- The squares of the `n` words at `d`, two words apart. -/
def diagR (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | d, n + 1 => (word m base d).toNat * (word m base d).toNat + 2 ^ 64 * 2 ^ 64 * VG.Proof.X448.X86_64.diagR m base (d + 8) n

theorem sq_rec_arith {B a X c d : Nat} (h : X * X = 2 * B * c + d) :
    (a + B * X) * (a + B * X) = 2 * B * (a * X + B * B * c) + (a * a + B * B * d) := by
  calc (a + B * X) * (a + B * X) = a * a + 2 * B * (a * X) + B * B * (X * X) := by grind
    _ = _ := by rw [h]; grind

/-- A square: twice the cross products, a word up, plus the squares. -/
theorem sq_rec (m : Mem) (base : Addr) : ∀ n d,
    mv m base d n * mv m base d n = 2 * 2 ^ 64 * VG.Proof.X448.X86_64.crossR m base d n + VG.Proof.X448.X86_64.diagR m base d n
  | 0, _ => rfl
  | n + 1, d => by
    rw [mv, VG.Proof.X448.X86_64.crossR, VG.Proof.X448.X86_64.diagR]; exact VG.Proof.X448.X86_64.sq_rec_arith (VG.Proof.X448.X86_64.sq_rec m base n (d + 8))

theorem sqRows_arith {M P B w1 w2 R' R aA cr C : Nat} (inv : M + P * (R + (aA + B * B * cr)) = C)
    (e : w1 + B * (w2 + B * R') = R + aA) :
    M + P * (w1 + B * w2) + P * B * B * (R' + cr) = C :=
  calc M + P * (w1 + B * w2) + P * B * B * (R' + cr)
      _ = M + P * ((w1 + B * (w2 + B * R')) + B * B * cr) := by grind
      _ = C := by rw [e, ← inv]; grind

theorem pow_two_succ (n : Nat) : 2 ^ (64 * (2 * (n + 1))) = 2 ^ (64 * (2 * n)) * 2 ^ 64 * 2 ^ 64 := by
  rw [show 64 * (2 * (n + 1)) = 64 * (2 * n) + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]

theorem mv_two (m : Mem) (base : Addr) (d : Nat) :
    mv m base d 2 = (word m base d).toNat + 2 ^ 64 * (word m base (d + 8)).toNat := by
  simp only [mv, Nat.mul_zero, Nat.add_zero]

/-- The six rows of cross products: the words `1–12` of the cross products
at `h 1`. -/
theorem sqRows_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a)
    (hz : rv s (wins 1 6) = 0) :
    WP isa (.block ((List.range 6).flatMap (sqRow a))) s fun t =>
      KeepsR clob s t ∧ Outside base (h 1) 96 s.mem t.mem ∧
      mv t.mem base (h 1) 12 = VG.Proof.X448.X86_64.crossR s.mem base a 7 := by
  have ha' : a + 56 ≤ 1536 := ha
  let inv := fun n (t : State) => KeepsR clob s t ∧ Outside base (h 1) (16 * n) s.mem t.mem ∧
    mv t.mem base (h 1) (2 * n) + 2 ^ (64 * (2 * n)) *
      (rv t (wins (2 * n + 1) (6 - n)) + VG.Proof.X448.X86_64.crossR s.mem base (a + 8 * n) (7 - n)) =
      VG.Proof.X448.X86_64.crossR s.mem base a 7
  have step : ∀ n t, n < 6 → inv n t → WP isa (.block (sqRow a n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tout, tv⟩
    have ht : Scr t base := hs.of_keepsR tk (by decide)
    refine WP.mono (VG.Proof.X448.X86_64.sqRow_ok ht ha (by omega)) fun t' ⟨e, k', out'⟩ => ⟨tk.trans k', ?_, ?_⟩
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        (out'.mono (by simp only [h]; omega) (by simp only [h]; omega))
    · have m1 : mv t'.mem base (h 1) (2 * n) = mv t.mem base (h 1) (2 * n) :=
        out'.mv (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega)
      have w2 : mv t'.mem base (h 1 + 8 * (2 * n)) 2 = (word t'.mem base (h (2 * n + 1))).toNat +
          2 ^ 64 * (word t'.mem base (h (2 * n + 2))).toNat := by
        rw [VG.Proof.X448.X86_64.mv_two, show h 1 + 8 * (2 * n) = h (2 * n + 1) by simp only [h]; omega,
          show h (2 * n + 1) + 8 = h (2 * n + 2) by simp only [h]; omega]
      have b1 : word t.mem base (a + 8 * n) = word s.mem base (a + 8 * n) :=
        tout.word (Or.inl (by simp only [h, ACC]; omega)) (by omega)
      have a1 : mv t.mem base (a + 8 * (n + 1)) (6 - n) = mv s.mem base (a + 8 * (n + 1)) (6 - n) :=
        tout.mv (Or.inl (by simp only [h, ACC]; omega)) (by omega)
      have cr : VG.Proof.X448.X86_64.crossR s.mem base (a + 8 * n) (7 - n) =
          (word s.mem base (a + 8 * n)).toNat * mv s.mem base (a + 8 * (n + 1)) (6 - n) +
            2 ^ 64 * 2 ^ 64 * VG.Proof.X448.X86_64.crossR s.mem base (a + 8 * (n + 1)) (6 - n) := by
        rw [show 7 - n = 6 - n + 1 by omega, VG.Proof.X448.X86_64.crossR, show a + 8 * n + 8 = a + 8 * (n + 1) by omega]
      rw [b1, a1] at e
      rw [cr] at tv
      show mv t'.mem base (h 1) (2 * (n + 1)) + 2 ^ (64 * (2 * (n + 1))) *
        (rv t' (wins (2 * (n + 1) + 1) (6 - (n + 1))) +
          VG.Proof.X448.X86_64.crossR s.mem base (a + 8 * (n + 1)) (7 - (n + 1))) = VG.Proof.X448.X86_64.crossR s.mem base a 7
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega, show 6 - (n + 1) = 5 - n by omega,
        show 7 - (n + 1) = 6 - n by omega, show 2 * (n + 1) = 2 * n + 2 by omega, mv_add, m1, w2,
        show 2 * n + 2 = 2 * (n + 1) by omega, VG.Proof.X448.X86_64.pow_two_succ]
      exact VG.Proof.X448.X86_64.sqRows_arith (B := 2 ^ 64) tv e
  refine WP.mono (wp_range_flatMap (M := isa) (N := 6) inv step 6 (by decide) s
    ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul, mv, hz,
        Nat.zero_add]⟩)
    fun t ⟨tk, tout, tv⟩ => ⟨tk, tout, ?_⟩
  have : VG.Proof.X448.X86_64.crossR s.mem base (a + 8 * 6) (7 - 6) = 0 := by simp [VG.Proof.X448.X86_64.crossR, mv]
  generalize 2 ^ (64 * (2 * 6)) = Q at tv
  rw [this, show wins (2 * 6 + 1) (6 - 6) = [] from rfl, rv, Nat.zero_add, Nat.mul_zero,
    Nat.add_zero] at tv
  exact tv

/-! ## Doubling and the squares -/

/-- `mulx hi, lo, r`. -/
theorem mulx_reg_ok (s : State) {hi lo r : Reg} (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo (.reg r)]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * (s.gpr r).toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execMulx, VG.X86_64.readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), RegUpd.cf_setReg, VG.Proof.X448.X86_64.of_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨mul_halves _ _, (by trivial), (by trivial), fun r' hr => ?_, (by trivial), (by trivial),
    (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

theorem dbl_arith {B T0 T1 lo hi dd c o c1 o1 c2 o2 x8 x8' x9 x9' : Nat} (e1 : lo + B * hi = dd)
    (e2 : x8 + B * c1 = T0 + T0 + c) (e3 : x8' + B * o1 = x8 + lo + o)
    (e4 : x9 + B * c2 = T1 + T1 + c1) (e5 : x9' + B * o2 = x9 + hi + o1) :
    x8' + B * x9' + B * B * (c2 + o2) = 2 * (T0 + B * T1) + dd + c + o :=
  calc x8' + B * x9' + B * B * (c2 + o2)
      _ = x8' + B * (x9' + B * o2) + B * B * c2 := by grind
      _ = (x8' + B * o1) + B * hi + B * (x9 + B * c2) := by rw [e5]; grind
      _ = (x8 + B * c1) + (lo + B * hi) + o + 2 * B * T1 := by rw [e3, e4]; grind
      _ = _ := by rw [e2, e1]; grind

/-- A load, the flags unchanged. -/
theorem ld_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) (r : Reg) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun s' =>
      s'.gpr r = word s.mem base d ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, VG.Proof.X448.X86_64.of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- A store, the flags unchanged. -/
theorem st_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun s' =>
      word s'.mem base d = s.gpr r ∧ Outside base d 8 s.mem s'.mem ∧ (∀ r', s'.gpr r' = s.gpr r') ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [WP.block_cons_iff]
  refine ⟨{ s with mem := s.mem.writeW (off base d) (s.gpr r) }, by
    have hw := hs.write (d := d) (n := 8) (by omega)
    simp only [exec, ea_sc, hs.rdi, State.store64, hw, ite_true],
    WP.block_nil ⟨word_writeW_self _ _ _ _, writeW_outside _ _ _ (by omega), fun _ => rfl, rfl, rfl,
      rfl, rfl⟩⟩

theorem dblRow_eq (a i : Nat) : dblRow a i =
    ([.mov .rdx (.mem (sc (a + 8 * i)))] : List Instr) ++
    (([.mulx .rcx .rax (.reg .rdx)] : List Instr) ++ (([.mov .r8 (.mem (sc (h (2 * i))))] : List Instr) ++
    (([.adcx .r8 (.reg .r8)] : List Instr) ++ (([.adox .r8 (.reg .rax)] : List Instr) ++
    (([.mov .r9 (.mem (sc (h (2 * i + 1))))] : List Instr) ++ (([.adcx .r9 (.reg .r9)] : List Instr) ++
    (([.adox .r9 (.reg .rcx)] : List Instr) ++
    (([.store (sc (h (2 * i))) .r8] : List Instr) ++ ([.store (sc (h (2 * i + 1))) .r9] : List Instr))))))))) :=
  rfl

/-- Words `2i` and `2i + 1`: those of the cross products doubled, plus
`a_i²`, plus the carries in. -/
theorem dblRow_ok {t : State} {base : Addr} (hs : Scr t base) {a i : Nat} (ha : Slot a) (hi : i < 7)
    {c o : Bool} (hc : t.cf = some c) (ho : t.of = some o) :
    WP isa (.block (dblRow a i)) t fun t' => ∃ c' o' : Bool, t'.cf = some c' ∧ t'.of = some o' ∧
      (word t'.mem base (h (2 * i))).toNat + 2 ^ 64 * (word t'.mem base (h (2 * i + 1))).toNat +
        2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * ((word t.mem base (h (2 * i))).toNat + 2 ^ 64 * (word t.mem base (h (2 * i + 1))).toNat) +
          (word t.mem base (a + 8 * i)).toNat * (word t.mem base (a + 8 * i)).toNat + c.toNat +
            o.toNat ∧
      KeepsR clob t t' ∧ Outside base (h (2 * i)) 16 t.mem t'.mem := by
  have ha' : a + 56 ≤ 1536 := ha
  have hh0 : h (2 * i) + 8 ≤ 8192 := by simp only [h, ACC]; omega
  have hh1 : h (2 * i + 1) + 8 ≤ 8192 := by simp only [h, ACC]; omega
  rw [VG.Proof.X448.X86_64.dblRow_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.ld_ok hs (d := a + 8 * i) (by omega) .rdx) fun s1 ⟨d1, c1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulx_reg_ok s1 (hi := .rcx) (lo := .rax) (r := .rdx) (by decide))
    fun s2 ⟨e2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.ld_ok hs2 hh0 .r8) fun s3 ⟨t3, c3, o3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adcx_ok s3 (x := .r8) (r := .r8) (c3.trans (c2.trans (c1.trans hc))))
    fun s4 ⟨cc4, hc4, o4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adox_ok s4 (x := .r8) (r := .rax) (o4.trans (o3.trans (o2.trans (o1.trans ho)))))
    fun s5 ⟨oo5, ho5, c5, e5, k5⟩ => ?_
  have hs5 := (hs3.of_keeps k4 (by decide)).of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.ld_ok hs5 hh1 .r9) fun s6 ⟨t6, c6, o6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adcx_ok s6 (x := .r9) (r := .r9) (c6.trans (c5.trans hc4)))
    fun s7 ⟨cc7, hc7, o7, e7, k7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adox_ok s7 (x := .r9) (r := .rcx) (o7.trans (o6.trans ho5)))
    fun s8 ⟨oo8, ho8, c8, e8, k8⟩ => ?_
  have hs8 := (hs6.of_keeps k7 (by decide)).of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.st_ok hs8 hh0 .r8) fun s9 ⟨w9, out9, g9, c9, o9, rd9, wr9⟩ => ?_
  have hs9 : Scr s9 base := ⟨(g9 _).trans hs8.rdi, wr9 ▸ hs8.wr, hs8.nowrap⟩
  refine WP.mono (VG.Proof.X448.X86_64.st_ok hs9 hh1 .r9) fun s10 ⟨w10, out10, g10, c10, o10, rd10, wr10⟩ =>
    ⟨cc7, oo8, c10.trans (c9.trans (c8.trans hc7)), o10.trans (o9.trans ho8), ?_, ?_, ?_⟩
  · have m2 : s2.mem = t.mem := k2.2.1.trans k1.2.1
    have m5 : s5.mem = t.mem := k5.2.1.trans (k4.2.1.trans (k3.2.1.trans m2))
    have ax : s4.gpr .rax = s2.gpr .rax := by rw [k4.1 _ (by decide), k3.1 _ (by decide)]
    have cx : s7.gpr .rcx = s2.gpr .rcx := by
      rw [k7.1 _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide),
        k3.1 _ (by decide)]
    have r8 : s8.gpr .r8 = s5.gpr .r8 := by
      rw [k8.1 _ (by decide), k7.1 _ (by decide), k6.1 _ (by decide)]
    have r9 : s9.gpr .r9 = s8.gpr .r9 := g9 _
    have W0 : word s10.mem base (h (2 * i)) = s5.gpr .r8 := by
      rw [out10.word (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega), w9, r8]
    have W1 : word s10.mem base (h (2 * i + 1)) = s8.gpr .r9 := by rw [w10, r9]
    rw [m2] at t3
    rw [m5] at t6
    rw [d1] at e2
    rw [ax] at e5
    rw [cx] at e8
    rw [t3] at e4
    rw [t6] at e7
    rw [W0, W1]
    exact VG.Proof.X448.X86_64.dbl_arith (B := 2 ^ 64) e2 e4 e5 e7 e8
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have := fun (l : List Reg) (hl : ∀ x ∈ l, x ∈ clob) => (fun h => hr (hl r h) : r ∉ l)
      rw [g10, g9, k8.1 r (this _ (by decide)), k7.1 r (this _ (by decide)),
        k6.1 r (this _ (by decide)), k5.1 r (this _ (by decide)), k4.1 r (this _ (by decide)),
        k3.1 r (this _ (by decide)), k2.1 r (this _ (by decide)), k1.1 r (this _ (by decide))]
    · rw [rd10, rd9, k8.2.2.1, k7.2.2.1, k6.2.2.1, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1,
        k1.2.2.1]
    · rw [wr10, wr9, k8.2.2.2, k7.2.2.2, k6.2.2.2, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2,
        k1.2.2.2]
  · have m8 : s8.mem = t.mem := k8.2.1.trans (k7.2.1.trans (k6.2.1.trans (k5.2.1.trans
      (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))))))
    rw [← m8]
    exact (out9.mono (Nat.le_refl _) (by omega)).trans
      (out10.mono (by simp only [h]; omega) (by simp only [h]; omega))

theorem dbls_arith {M P B W0 W1 c' o' T0 T1 aa c o X D R : Nat}
    (inv : M + P * (c + o + (2 * (T0 + B * (T1 + B * X)) + (aa + B * B * D))) = R)
    (e : W0 + B * W1 + B * B * (c' + o') = 2 * (T0 + B * T1) + aa + c + o) :
    M + P * (W0 + B * W1) + P * B * B * (c' + o' + (2 * X + D)) = R :=
  calc M + P * (W0 + B * W1) + P * B * B * (c' + o' + (2 * X + D))
      _ = M + P * ((W0 + B * W1 + B * B * (c' + o')) + B * B * (2 * X + D)) := by grind
      _ = R := by rw [e, ← inv]; grind

/-- The seven steps of doubling and squares: `2 · [h 0] + diagR` in
`[h 0]`, the carries out. -/
theorem dbls_ok {u : State} {base : Addr} (hs : Scr u base) {a : Nat} (ha : Slot a)
    (hc : u.cf = some false) (ho : u.of = some false) :
    WP isa (.block ((List.range 7).flatMap (dblRow a))) u fun t => ∃ c o : Bool,
      KeepsR clob u t ∧ Outside base (h 0) 112 u.mem t.mem ∧
      mv t.mem base (h 0) (2 * 7) + 2 ^ (64 * (2 * 7)) * (c.toNat + o.toNat) =
        2 * mv u.mem base (h 0) 14 + VG.Proof.X448.X86_64.diagR u.mem base a 7 := by
  have ha' : a + 56 ≤ 1536 := ha
  let inv := fun n (t : State) => ∃ c o : Bool, t.cf = some c ∧ t.of = some o ∧ KeepsR clob u t ∧
    Outside base (h 0) (16 * n) u.mem t.mem ∧
    mv t.mem base (h 0) (2 * n) + 2 ^ (64 * (2 * n)) * (c.toNat + o.toNat +
      (2 * mv u.mem base (h (2 * n)) (14 - 2 * n) + VG.Proof.X448.X86_64.diagR u.mem base (a + 8 * n) (7 - n))) =
      2 * mv u.mem base (h 0) 14 + VG.Proof.X448.X86_64.diagR u.mem base a 7
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block (dblRow a n)) t (inv (n + 1)) := by
    intro n t hn ⟨c, o, hc, ho, tk, tout, tv⟩
    have ht : Scr t base := hs.of_keepsR tk (by decide)
    refine WP.mono (VG.Proof.X448.X86_64.dblRow_ok ht ha hn hc ho) fun t' ⟨c', o', hc', ho', e, k', out'⟩ =>
      ⟨c', o', hc', ho', tk.trans k', ?_, ?_⟩
    · exact (tout.mono (Nat.le_refl _) (by omega)).trans
        (out'.mono (by simp only [h]; omega) (by simp only [h]; omega))
    · have m1 : mv t'.mem base (h 0) (2 * n) = mv t.mem base (h 0) (2 * n) :=
        out'.mv (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega)
      have w2 : mv t'.mem base (h 0 + 8 * (2 * n)) 2 = (word t'.mem base (h (2 * n))).toNat +
          2 ^ 64 * (word t'.mem base (h (2 * n + 1))).toNat := by
        rw [VG.Proof.X448.X86_64.mv_two, show h 0 + 8 * (2 * n) = h (2 * n) by simp only [h]; omega,
          show h (2 * n) + 8 = h (2 * n + 1) by simp only [h]; omega]
      have T0 : word t.mem base (h (2 * n)) = word u.mem base (h (2 * n)) :=
        tout.word (Or.inr (by simp only [h]; omega)) (by simp only [h, ACC]; omega)
      have T1 : word t.mem base (h (2 * n + 1)) = word u.mem base (h (2 * n + 1)) :=
        tout.word (Or.inr (by simp only [h]; omega)) (by simp only [h, ACC]; omega)
      have A1 : word t.mem base (a + 8 * n) = word u.mem base (a + 8 * n) :=
        tout.word (Or.inl (by simp only [h, ACC]; omega)) (by omega)
      have mu : mv u.mem base (h (2 * n)) (14 - 2 * n) = (word u.mem base (h (2 * n))).toNat +
          2 ^ 64 * ((word u.mem base (h (2 * n + 1))).toNat +
            2 ^ 64 * mv u.mem base (h (2 * (n + 1))) (14 - 2 * (n + 1))) := by
        rw [show 14 - 2 * n = 14 - 2 * (n + 1) + 1 + 1 by omega, mv, mv,
          show h (2 * n) + 8 = h (2 * n + 1) by simp only [h]; omega,
          show h (2 * n + 1) + 8 = h (2 * (n + 1)) by simp only [h]; omega]
      have dg : VG.Proof.X448.X86_64.diagR u.mem base (a + 8 * n) (7 - n) =
          (word u.mem base (a + 8 * n)).toNat * (word u.mem base (a + 8 * n)).toNat +
            2 ^ 64 * 2 ^ 64 * VG.Proof.X448.X86_64.diagR u.mem base (a + 8 * (n + 1)) (7 - (n + 1)) := by
        rw [show 7 - n = 7 - (n + 1) + 1 by omega, VG.Proof.X448.X86_64.diagR,
          show a + 8 * n + 8 = a + 8 * (n + 1) by omega]
      rw [T0, T1, A1] at e
      rw [mu, dg] at tv
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, mv_add, m1, w2,
        show 2 * n + 2 = 2 * (n + 1) by omega, VG.Proof.X448.X86_64.pow_two_succ]
      exact VG.Proof.X448.X86_64.dbls_arith (B := 2 ^ 64) tv e
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) u
    ⟨false, false, hc, ho, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul, mv,
        Bool.toNat_false, Nat.zero_add]⟩)
    fun t ⟨c, o, _, _, tk, tout, tv⟩ => ⟨c, o, tk, tout, ?_⟩
  generalize 2 ^ (64 * (2 * 7)) = Q at tv ⊢
  rw [show mv u.mem base (h (2 * 7)) 0 = 0 from rfl, show VG.Proof.X448.X86_64.diagR u.mem base (a + 8 * 7) 0 = 0 from rfl,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero] at tv
  exact tv

theorem crossR_out {m m' : Mem} {base : Addr} {o n' : Nat} (hO : Outside base o n' m m')
    (ho : o ≤ 8192) : ∀ n d, d + 8 * n ≤ o → VG.Proof.X448.X86_64.crossR m' base d n = VG.Proof.X448.X86_64.crossR m base d n
  | 0, _, _ => rfl
  | n + 1, d, hd => by
    rw [VG.Proof.X448.X86_64.crossR, VG.Proof.X448.X86_64.crossR, hO.word (Or.inl (by omega)) (by omega),
      hO.mv (Or.inl (by omega)) (by omega), VG.Proof.X448.X86_64.crossR_out hO ho n (d + 8) (by omega)]

theorem diagR_out {m m' : Mem} {base : Addr} {o n' : Nat} (hO : Outside base o n' m m')
    (ho : o ≤ 8192) : ∀ n d, d + 8 * n ≤ o → VG.Proof.X448.X86_64.diagR m' base d n = VG.Proof.X448.X86_64.diagR m base d n
  | 0, _, _ => rfl
  | n + 1, d, hd => by
    rw [VG.Proof.X448.X86_64.diagR, VG.Proof.X448.X86_64.diagR, hO.word (Or.inl (by omega)) (by omega),
      VG.Proof.X448.X86_64.diagR_out hO ho n (d + 8) (by omega)]

theorem sqrX_eq (o a : Nat) : sqrX o a = ((wins 1 6).map fun r => .mov32 r (.imm 0)) ++
    (([.store (sc (h 0)) (win 1 0)] : List Instr) ++ (([.store (sc (h 13)) (win 1 0)] : List Instr) ++
    ((List.range 6).flatMap (sqRow a) ++ (([clear] : List Instr) ++
    ((List.range 7).flatMap (dblRow a) ++ reduce o))))) := by
  simp only [sqrX, List.append_assoc]; rfl

theorem wins16_clob : ∀ r ∈ wins 1 6, r ∈ clob := by decide

/-- `[o] = [a]²`, by rows of cross products. -/
theorem sqrX_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  have ho' : o + 56 ≤ 1536 := ho
  rw [VG.Proof.X448.X86_64.sqrX_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.zeros_ok (wins 1 6) s) fun s1 ⟨z1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have z10 : s1.gpr (win 1 0) = 0 := z1 _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.st_ok hs1 (d := h 0) (by simp only [h, ACC]; omega) (win 1 0))
    fun s2 ⟨w2, out2, g2, _, _, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.st_ok hs2 (d := h 13) (by simp only [h, ACC]; omega) (win 1 0))
    fun s3 ⟨w3, out3, g3, _, _, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  have hz : rv s3 (wins 1 6) = 0 :=
    VG.Proof.X448.X86_64.rv_zero s3 _ fun r hr => by rw [g3, g2]; exact z1 r hr
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqRows_ok hs3 ha hz) fun s4 ⟨k4, out4, v4⟩ => ?_
  have hs4 := hs3.of_keepsR k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.clear_ok s4) fun s5 ⟨_, c5, o5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.dbls_ok hs5 ha c5 o5) fun s6 ⟨c, o6, k6, out6, v6⟩ => ?_
  have hs6 := hs5.of_keepsR k6 (by decide)
  refine WP.mono (reduce_ok hs6 ho) fun s7 ⟨e7, g7, rd7, wr7, out7⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    rw [g7 r hr, k6.1 r hr, k5.1 r (by simp; exact fun e => hr (e ▸ by decide)), k4.1 r hr, g3, g2,
      k1.1 r fun h => hr (VG.Proof.X448.X86_64.wins16_clob r h)]
  · rw [rd7, k6.2.1, k5.2.2.1, k4.2.1, rd3, rd2, k1.2.2.1]
  · rw [wr7, k6.2.2, k5.2.2.2, k4.2.2, wr3, wr2, k1.2.2.2]
  · rw [← k1.2.1]
    have A : ∀ {x n : Nat} {m m' : Mem}, Outside base x n m m' → ACC ≤ x → x + n ≤ ACC + 112 →
        Outside2 base o 56 ACC 112 m m' := fun h₁ h₂ h₃ => (h₁.mono h₂ h₃).right o 56
    refine (A out2 (by simp only [h]; omega) (by simp only [h]; omega)).trans
      ((A out3 (by simp only [h]; omega) (by simp only [h, ACC]; omega)).trans
      ((A out4 (by simp only [h]; omega) (by simp only [h]; omega)).trans ?_))
    rw [← k5.2.1]
    exact (A out6 (by simp only [h]; omega) (by simp only [h]; omega)).trans (out7.left ACC 112)
  · -- the value
    have m5 : s5.mem = s4.mem := k5.2.1
    have m1 : s1.mem = s.mem := k1.2.1
    have h0 : word s4.mem base (h 0) = 0 := by
      rw [out4.word (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega),
        out3.word (Or.inl (by simp only [h]; omega)) (by simp only [h, ACC]; omega), w2, z10]
    have h13 : word s4.mem base (h 13) = 0 := by
      rw [out4.word (Or.inr (by simp only [h]; omega)) (by simp only [h, ACC]; omega), w3, g2, z10]
    have T : mv s4.mem base (h 0) 14 = 2 ^ 64 * VG.Proof.X448.X86_64.crossR s3.mem base a 7 := by
      rw [show (14 : Nat) = 12 + 1 + 1 from rfl, mv, show h 0 + 8 = h 1 from rfl, mv_add, v4,
        show h 1 + 8 * 12 = h 13 from rfl, mv, h0, h13]
      simp only [mv, toNat_zero64, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    have Os : Outside base ACC 112 s.mem s3.mem := by
      rw [← m1]
      exact (out2.mono (by simp only [h]; omega) (by simp only [h]; omega)).trans
        (out3.mono (by simp only [h]; omega) (by simp only [h, ACC]; omega))
    have O4 : Outside base ACC 112 s.mem s4.mem :=
      Os.trans (out4.mono (by simp only [h]; omega) (by simp only [h]; omega))
    rw [m5, T, VG.Proof.X448.X86_64.diagR_out O4 (by decide) 7 a (by omega), VG.Proof.X448.X86_64.crossR_out Os (by decide) 7 a (by omega)] at v6
    have sq := VG.Proof.X448.X86_64.sq_rec s.mem base 7 a
    rw [show 2 * (2 ^ 64 * VG.Proof.X448.X86_64.crossR s.mem base a 7) = 2 * 2 ^ 64 * VG.Proof.X448.X86_64.crossR s.mem base a 7 from
      (Nat.mul_assoc _ _ _).symm, ← sq] at v6
    have hlt := prod_lt (mv_lt s.mem base a 7) (mv_lt s.mem base a 7)
    rw [show 7 + 7 = 2 * 7 from rfl] at hlt
    have hP : mv s6.mem base (h 0) (2 * 7) = mv s.mem base a 7 * mv s.mem base a 7 := by
      generalize 2 ^ (64 * (2 * 7)) = Q at v6 hlt
      generalize mv s.mem base a 7 * mv s.mem base a 7 = S at v6 hlt
      cases c <;> cases o6 <;> simp only [Bool.toNat_false, Bool.toNat_true] at v6 <;> omega
    rw [show h 0 = ACC from rfl, show 2 * 7 = 7 + 7 from rfl, mv_add] at hP
    rw [show ACC + 56 = ACC + 8 * 7 from rfl, show (448 : Nat) = 64 * 7 from rfl, hP] at e7
    exact toFe_mul e7

/-- The field multiplications with BMI2 and ADX. -/
theorem adx_ok : FieldOk adx where
  mul hs _ _ _ ho ha hb := VG.Proof.X448.X86_64.mulX_ok hs ho ha hb
  sqr hs _ _ ho ha := VG.Proof.X448.X86_64.sqrX_ok hs ho ha
  a24 hs _ _ ho ha := WP.mono (mulSmall_ok hs ho ha (k := a24) (by decide)) fun _ ⟨h, e⟩ =>
    ⟨h, toFe_a24 e⟩

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Adx.Verified`. -/
section

/-!
# X448 on x86-64 with BMI2 and ADX: `Verified`

The proof of `vg_x448` (`Proof/X448/X86_64/Verified.lean`) for the field
multiplications `adx` (`adx_ok`): correctness from `correct`, constant time by
taint tracking (the only branches are on the loop counters, and every address
is an argument plus a constant or a counter), satisfiability, and the shared
contract.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

theorem x448Adx_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448Adx s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct VG.Proof.X448.X86_64.adx_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x448Adx_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448Adx := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448Adx_verified :
    Verified X86_64.target Impl.X448.X86_64.x448Adx (Spec.X448.x448Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.X448.X86_64.x448Adx_ok VG.Proof.X448.X86_64.x448Adx_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs,
      Proof.X448.x448X86_64] [satState] using satState)

end VG.Proof.X448.X86_64

end
