module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Prune64
import VerifiedGarbage.Proof.Ed25519.Expanded
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Ed25519's whole functions on PPC64LE: pruning, and copies

`prune f d o` stores at `o(F)` the first half of the digest at `d(F)`
pruned, four 64-bit words (`prune_ok`): the shifts clear the low word's 3
low bits and the high word's top bit, and an `or` sets bit 254. `copy32` and
`copyIn` copy 32 bytes word by word.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole VG.Proof.X25519.PPC64LE

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_ldd {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 8) (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_stdd {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8) (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

theorem shr_shl3 (x : BitVec 64) : x >>> 3 <<< 3 = x &&& BitVec.ofNat 64 (2 ^ 64 - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat,
    show (2 ^ 64 - 8) % 2 ^ 64 = 2 ^ 64 - 8 from rfl, Proof.Ed25519.Prune64.and_sub8 _ 64 (by omega_arith),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  simp only [show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega_arith

theorem shl_shr2 (x : BitVec 64) : x <<< 2 >>> 2 = x &&& BitVec.ofNat 64 (2 ^ 62 - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat,
    show (2 ^ 62 - 1) % 2 ^ 64 = 2 ^ 62 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega_arith

theorem lis_bit62 : ((0x4000 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 <<< 32 = BitVec.ofNat 64 (2 ^ 62) := by
  decide

/-- The pruning, with `F` in `f`: the area `[F + d, F + d + 64)` is readable, and
`[F + o, F + o + 32)` writable and apart from the first half of it. -/
theorem prune_ok {t : State} {f : Reg} {F : Addr} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hf0 : f ≠ .r0) (hf : f ≠ .r8 ∧ f ≠ .r9) (hF : t.gpr f = F)
    (hd : d + 64 < 2 ^ 15 ∧ d % 8 = 0) (ho : o + 32 < 2 ^ 15 ∧ o % 8 = 0) (hdo : d + 32 ≤ o ∨ o + 32 ≤ d)
    (hr : ∀ k < 4, InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 (d + 8 * k)) 8)
    (hw : ∀ k < 4, InRegions t.wr (F + BitVec.ofNat 64 (o + 8 * k)) 8)
    (k : ∀ u, Rest [.r8, .r9] t u → Frame [⟨F + BitVec.ofNat 64 o, 32⟩] t.mem u.mem →
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (F + BitVec.ofNat 64 o) 32) =
        Spec.Ed25519.prune (Spec.Ed25519.bytesAt t.mem (F + BitVec.ofNat 64 d) 64) →
      WP isa (.block rest) u Q) :
    WP isa (.block (prune f d o ++ rest)) t Q := by
  unfold prune
  simp only [List.cons_append, List.nil_append]
  obtain ⟨f8, f9⟩ := hf
  -- The words read are not those written.
  have sep : ∀ i < 4, ∀ j < 4, Mem.Sep (F + BitVec.ofNat 64 (d + 8 * i)) 8 (F + BitVec.ofNat 64 (o + 8 * j)) 8 :=
    fun i hi j hj => Offset.sep F (by omega_arith) (by omega_arith) (by omega_arith)
  have sep' : ∀ i < 4, ∀ j < 4, i ≠ j → Mem.Sep (F + BitVec.ofNat 64 (o + 8 * i)) 8 (F + BitVec.ofNat 64 (o + 8 * j)) 8 :=
    fun i hi j hj hij => Offset.sep F (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_ldd (a := F + BitVec.ofNat 64 (d + 8 * 0)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [hF]; simp) (hr 0 (by omega_arith))
    fun u₁ h₁ => wp_lsr (by decide) fun u₂ h₂ => wp_lsl (by decide) fun u₃ h₃ => ?_
  have e₃ : u₃.gpr f = F := by rw [h₃.other _ f8, h₂.other _ f8, h₁.other _ f8, hF]
  refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * 0)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₃]; simp)
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact hw 0 (by omega_arith)) fun u₄ h₄ => ?_
  have e₄ : u₄.gpr f = F := by rw [h₄.gpr, e₃]
  refine wp_ldd (a := F + BitVec.ofNat 64 (d + 8 * 1)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₄])
    (by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hr 1 (by omega_arith)) fun u₅ h₅ => ?_
  have e₅ : u₅.gpr f = F := by rw [h₅.other _ f8, e₄]
  refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * 1)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₅])
    (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 1 (by omega_arith)) fun u₆ h₆ => ?_
  have e₆ : u₆.gpr f = F := by rw [h₆.gpr, e₅]
  refine wp_ldd (a := F + BitVec.ofNat 64 (d + 8 * 2)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₆])
    (by rw [h₆.rd, h₆.wr, h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hr 2 (by omega_arith))
    fun u₇ h₇ => ?_
  have e₇ : u₇.gpr f = F := by rw [h₇.other _ f8, e₆]
  refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * 2)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₇])
    (by rw [h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 2 (by omega_arith)) fun u₈ h₈ => ?_
  have e₈ : u₈.gpr f = F := by rw [h₈.gpr, e₇]
  refine wp_ldd (a := F + BitVec.ofNat 64 (d + 8 * 3)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₈])
    (by rw [h₈.rd, h₈.wr, h₇.rd, h₇.wr, h₆.rd, h₆.wr, h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr,
      h₁.rd, h₁.wr]; exact hr 3 (by omega_arith))
    fun u₉ h₉ => wp_lsl (by decide) fun u₁₀ h₁₀ => wp_lsr (by decide) fun u₁₁ h₁₁ =>
      wp_lis fun u₁₂ h₁₂ => wp_lsl (by decide) fun u₁₃ h₁₃ => wp_or fun u₁₄ h₁₄ => ?_
  have e₁₄ : u₁₄.gpr f = F := by
    rw [h₁₄.other _ f8, h₁₃.other _ f9, h₁₂.other _ f9, h₁₁.other _ f8, h₁₀.other _ f8, h₉.other _ f8, e₈]
  refine wp_stdd (a := F + BitVec.ofNat 64 (o + 8 * 3)) hf0 ⟨by omega_arith, by omega_arith⟩ (by rw [e₁₄])
    (by rw [h₁₄.wr, h₁₃.wr, h₁₂.wr, h₁₁.wr, h₁₀.wr, h₉.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
        exact hw 3 (by omega_arith)) fun u h => ?_
  -- The memories, and the words in them.
  have m₄ : u₄.mem = t.mem.writeW (F + BitVec.ofNat 64 (o + 8 * 0)) (u₃.gpr .r8) := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have m₆ : u₆.mem = u₄.mem.writeW (F + BitVec.ofNat 64 (o + 8 * 1)) (u₅.gpr .r8) := by rw [h₆.mem, h₅.mem]
  have m₈ : u₈.mem = u₆.mem.writeW (F + BitVec.ofNat 64 (o + 8 * 2)) (u₇.gpr .r8) := by rw [h₈.mem, h₇.mem]
  have m : u.mem = u₈.mem.writeW (F + BitVec.ofNat 64 (o + 8 * 3)) (u₁₄.gpr .r8) := by
    rw [h.mem, h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem]
  have rs : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i < 4 → j < 4 →
      (x.writeW (F + BitVec.ofNat 64 (o + 8 * j)) v).readW (F + BitVec.ofNat 64 (d + 8 * i)) 64 = x.readW (F + BitVec.ofNat 64 (d + 8 * i)) 64 :=
    fun x i j v hi hj => Mem.readW_writeW_sep (sep i hi j hj) (by decide)
  have rs' : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i < 4 → j < 4 → i ≠ j →
      (x.writeW (F + BitVec.ofNat 64 (o + 8 * j)) v).readW (F + BitVec.ofNat 64 (o + 8 * i)) 64 = x.readW (F + BitVec.ofNat 64 (o + 8 * i)) 64 :=
    fun x i j v hi hj hij => Mem.readW_writeW_sep (sep' i hi j hj hij) (by decide)
  have v₃ : u₃.gpr .r8 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 0)) 64 &&& BitVec.ofNat 64 (2 ^ 64 - 8) := by
    rw [h₃.gpr, h₂.gpr, h₁.gpr, shr_shl3]
  have v₅ : u₅.gpr .r8 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 1)) 64 := by
    rw [h₅.gpr, m₄, rs _ 1 0 _ (by omega_arith) (by omega_arith)]
  have v₇ : u₇.gpr .r8 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 2)) 64 := by
    rw [h₇.gpr, h₆.mem, h₅.mem, m₄, rs _ 2 1 _ (by omega_arith) (by omega_arith), rs _ 2 0 _ (by omega_arith) (by omega_arith)]
  have v₁₄ : u₁₄.gpr .r8 =
      (t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 3)) 64 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62) := by
    rw [h₁₄.gpr, h₁₃.other _ (by decide), h₁₂.other _ (by decide), h₁₁.gpr, h₁₀.gpr, h₉.gpr, h₁₃.gpr, h₁₂.gpr,
      lis_bit62, shl_shr2, h₈.mem, h₇.mem, m₆, m₄, rs _ 3 2 _ (by omega_arith) (by omega_arith),
      rs _ 3 1 _ (by omega_arith) (by omega_arith), rs _ 3 0 _ (by omega_arith) (by omega_arith)]
  have w₀ : u.mem.readW (F + BitVec.ofNat 64 (o + 8 * 0)) 64 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 0)) 64 &&& BitVec.ofNat 64 (2 ^ 64 - 8) := by
    rw [m, rs' _ 0 3 _ (by omega_arith) (by omega_arith) (by omega_arith), m₈, rs' _ 0 2 _ (by omega_arith) (by omega_arith) (by omega_arith),
      m₆, rs' _ 0 1 _ (by omega_arith) (by omega_arith) (by omega_arith), m₄, Mem.readW_writeW_self64, v₃]
  have w₁ : u.mem.readW (F + BitVec.ofNat 64 (o + 8 * 1)) 64 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 1)) 64 := by
    rw [m, rs' _ 1 3 _ (by omega_arith) (by omega_arith) (by omega_arith), m₈, rs' _ 1 2 _ (by omega_arith) (by omega_arith) (by omega_arith),
      m₆, Mem.readW_writeW_self64, v₅]
  have w₂ : u.mem.readW (F + BitVec.ofNat 64 (o + 8 * 2)) 64 = t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 2)) 64 := by
    rw [m, rs' _ 2 3 _ (by omega_arith) (by omega_arith) (by omega_arith), m₈, Mem.readW_writeW_self64, v₇]
  have w₃ : u.mem.readW (F + BitVec.ofNat 64 (o + 8 * 3)) 64 =
      (t.mem.readW (F + BitVec.ofNat 64 (d + 8 * 3)) 64 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62) := by
    rw [m, Mem.readW_writeW_self64, v₁₄]
  have ad : ∀ (a b : Nat), F + BitVec.ofNat 64 a + BitVec.ofNat 64 b = F + BitVec.ofNat 64 (a + b) :=
    fun a b => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have cont : ∀ j < 4, Region.Contains ⟨F + BitVec.ofNat 64 o, 32⟩ (F + BitVec.ofNat 64 (o + 8 * j)) (64 / 8) := fun j hj =>
    Offset.contains F (by omega_arith) (by omega_arith) (by omega_arith)
  refine k u ⟨fun r hr => ?_, ?_, ?_, ?_⟩ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h.gpr, h₁₄.other _ hr.1, h₁₃.other _ hr.2, h₁₂.other _ hr.2, h₁₁.other _ hr.1, h₁₀.other _ hr.1,
      h₉.other _ hr.1, h₈.gpr, h₇.other _ hr.1, h₆.gpr, h₅.other _ hr.1, h₄.gpr, h₃.other _ hr.1,
      h₂.other _ hr.1, h₁.other _ hr.1]
  · rw [h.rd, h₁₄.rd, h₁₃.rd, h₁₂.rd, h₁₁.rd, h₁₀.rd, h₉.rd, h₈.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h.wr, h₁₄.wr, h₁₃.wr, h₁₂.wr, h₁₁.wr, h₁₀.wr, h₉.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [h.sp, h₁₄.sp, h₁₃.sp, h₁₂.sp, h₁₁.sp, h₁₀.sp, h₉.sp, h₈.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  · rw [m, m₈, m₆, m₄]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cont 0 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (cont 1 (by omega_arith))).writeW (List.mem_singleton_self _) _ (cont 2 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (cont 3 (by omega_arith))
  · refine Proof.Ed25519.Prune64.prune_of_words ?_ ?_ ?_ ?_
    · simpa using w₀
    · rw [ad, ad]; simpa using w₁
    · rw [ad, ad]; simpa using w₂
    · rw [ad, ad]; simpa using w₃

/-! ## Copies -/

/-- 32 bytes from their four little-endian words. -/
theorem bytes32_of_words {m m' : Mem} {p q : Addr}
    (h : ∀ k < 4, m'.readW (q + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64) :
    Spec.Ed25519.bytesAt m' q 32 = Spec.Ed25519.bytesAt m p 32 := by
  simp only [Spec.Ed25519.bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ∀ x : Addr, x + BitVec.ofNat 64 i = x + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro x
    have e : BitVec.ofNat 64 i = BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1; omega_arith
    rw [e, BitVec.add_assoc]
  have hk : i / 8 < 4 := by omega_arith
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [ha q, ha p, Proof.Ed25519.readW_byte64 m' _ hj, Proof.Ed25519.readW_byte64 m _ hj, h _ hk]

/-- Four words copied from `da k(a)` to `db k(b)`, through `r8`, into the region `R`. -/
theorem copy_ok {t : State} {a b : Reg} {A B : Addr} {da db : Nat → Nat} {R : Region} {rest : List Instr}
    {Q : State → Prop} (ha0 : a ≠ .r0) (hb0 : b ≠ .r0) (ha8 : a ≠ .r8) (hb8 : b ≠ .r8)
    (hA : t.gpr a = A) (hB : t.gpr b = B)
    (hda : ∀ k < 4, da k < 2 ^ 15 ∧ da k % 4 = 0) (hdb : ∀ k < 4, db k < 2 ^ 15 ∧ db k % 4 = 0)
    (hr : ∀ k < 4, InRegions (t.rd ++ t.wr) (A + BitVec.ofNat 64 (da k)) 8)
    (hw : ∀ k < 4, InRegions t.wr (B + BitVec.ofNat 64 (db k)) 8)
    (hc : ∀ k < 4, R.Contains (B + BitVec.ofNat 64 (db k)) (64 / 8))
    (hs : ∀ i < 4, ∀ j < 4, Mem.Sep (A + BitVec.ofNat 64 (da i)) 8 (B + BitVec.ofNat 64 (db j)) 8)
    (hs' : ∀ i < 4, ∀ j < 4, i ≠ j → Mem.Sep (B + BitVec.ofNat 64 (db i)) 8 (B + BitVec.ofNat 64 (db j)) 8)
    (k : ∀ u, Rest [.r8] t u → Frame [R] t.mem u.mem →
      (∀ j < 4, u.mem.readW (B + BitVec.ofNat 64 (db j)) 64 = t.mem.readW (A + BitVec.ofNat 64 (da j)) 64) →
      WP isa (.block rest) u Q) :
    WP isa (.block (((List.range 4).flatMap fun k => [.load .d .r8 a (da k), .store .d .r8 b (db k)]) ++ rest)) t Q := by
  rw [show ((List.range 4).flatMap fun k => [Instr.load .d .r8 a (da k), .store .d .r8 b (db k)]) =
    [.load .d .r8 a (da 0), .store .d .r8 b (db 0), .load .d .r8 a (da 1), .store .d .r8 b (db 1),
      .load .d .r8 a (da 2), .store .d .r8 b (db 2), .load .d .r8 a (da 3), .store .d .r8 b (db 3)] from rfl]
  simp only [List.cons_append, List.nil_append]
  have rd : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i < 4 → j < 4 →
      (x.writeW (B + BitVec.ofNat 64 (db j)) v).readW (A + BitVec.ofNat 64 (da i)) 64 =
        x.readW (A + BitVec.ofNat 64 (da i)) 64 :=
    fun x i j v hi hj => Mem.readW_writeW_sep (hs i hi j hj) (by decide)
  have rd' : ∀ (x : Mem) (i j : Nat) (v : BitVec 64), i < 4 → j < 4 → i ≠ j →
      (x.writeW (B + BitVec.ofNat 64 (db j)) v).readW (B + BitVec.ofNat 64 (db i)) 64 =
        x.readW (B + BitVec.ofNat 64 (db i)) 64 :=
    fun x i j v hi hj hij => Mem.readW_writeW_sep (hs' i hi j hj hij) (by decide)
  refine wp_ldd ha0 (hda 0 (by omega_arith)) (by rw [hA]) (hr 0 (by omega_arith)) fun u₁ h₁ => ?_
  refine wp_stdd hb0 (hdb 0 (by omega_arith)) (by rw [h₁.other _ hb8, hB]) (by rw [h₁.wr]; exact hw 0 (by omega_arith))
    fun u₂ h₂ => ?_
  have g₂a : u₂.gpr a = A := by rw [h₂.gpr, h₁.other _ ha8, hA]
  have g₂b : u₂.gpr b = B := by rw [h₂.gpr, h₁.other _ hb8, hB]
  refine wp_ldd ha0 (hda 1 (by omega_arith)) (by rw [g₂a]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hr 1 (by omega_arith))
    fun u₃ h₃ => ?_
  refine wp_stdd hb0 (hdb 1 (by omega_arith)) (by rw [h₃.other _ hb8, g₂b])
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact hw 1 (by omega_arith)) fun u₄ h₄ => ?_
  have g₄a : u₄.gpr a = A := by rw [h₄.gpr, h₃.other _ ha8, g₂a]
  have g₄b : u₄.gpr b = B := by rw [h₄.gpr, h₃.other _ hb8, g₂b]
  refine wp_ldd ha0 (hda 2 (by omega_arith)) (by rw [g₄a])
    (by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hr 2 (by omega_arith)) fun u₅ h₅ => ?_
  refine wp_stdd hb0 (hdb 2 (by omega_arith)) (by rw [h₅.other _ hb8, g₄b])
    (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 2 (by omega_arith)) fun u₆ h₆ => ?_
  have g₆a : u₆.gpr a = A := by rw [h₆.gpr, h₅.other _ ha8, g₄a]
  have g₆b : u₆.gpr b = B := by rw [h₆.gpr, h₅.other _ hb8, g₄b]
  refine wp_ldd ha0 (hda 3 (by omega_arith)) (by rw [g₆a])
    (by rw [h₆.rd, h₆.wr, h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]
        exact hr 3 (by omega_arith)) fun u₇ h₇ => ?_
  refine wp_stdd hb0 (hdb 3 (by omega_arith)) (by rw [h₇.other _ hb8, g₆b])
    (by rw [h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact hw 3 (by omega_arith)) fun u h => ?_
  have v₁ : u₁.gpr .r8 = t.mem.readW (A + BitVec.ofNat 64 (da 0)) 64 := h₁.gpr
  have v₃ : u₃.gpr .r8 = t.mem.readW (A + BitVec.ofNat 64 (da 1)) 64 := by
    rw [h₃.gpr, h₂.mem, h₁.mem, rd _ 1 0 _ (by omega_arith) (by omega_arith)]
  have v₅ : u₅.gpr .r8 = t.mem.readW (A + BitVec.ofNat 64 (da 2)) 64 := by
    rw [h₅.gpr, h₄.mem, h₃.mem, h₂.mem, h₁.mem, rd _ 2 1 _ (by omega_arith) (by omega_arith), rd _ 2 0 _ (by omega_arith) (by omega_arith)]
  have v₇ : u₇.gpr .r8 = t.mem.readW (A + BitVec.ofNat 64 (da 3)) 64 := by
    rw [h₇.gpr, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, rd _ 3 2 _ (by omega_arith) (by omega_arith),
      rd _ 3 1 _ (by omega_arith) (by omega_arith), rd _ 3 0 _ (by omega_arith) (by omega_arith)]
  have m : u.mem = ((((t.mem.writeW (B + BitVec.ofNat 64 (db 0)) (u₁.gpr .r8)).writeW
      (B + BitVec.ofNat 64 (db 1)) (u₃.gpr .r8)).writeW (B + BitVec.ofNat 64 (db 2)) (u₅.gpr .r8)).writeW
      (B + BitVec.ofNat 64 (db 3)) (u₇.gpr .r8)) := by
    rw [h.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine k u ⟨fun r hr => ?_, ?_, ?_, ?_⟩ ?_ fun j hj => ?_
  · have hr' : r ≠ .r8 := by simpa using hr
    rw [h.gpr, h₇.other _ hr', h₆.gpr, h₅.other _ hr', h₄.gpr, h₃.other _ hr', h₂.gpr, h₁.other _ hr']
  · rw [h.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [h.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]
  · rw [m]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 0 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (hc 1 (by omega_arith))).writeW (List.mem_singleton_self _) _ (hc 2 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (hc 3 (by omega_arith))
  · rw [m]
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_arith
    rcases this with rfl | rfl | rfl | rfl
    · rw [rd' _ 0 3 _ (by omega_arith) (by omega_arith) (by omega_arith), rd' _ 0 2 _ (by omega_arith) (by omega_arith) (by omega_arith),
        rd' _ 0 1 _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64, v₁]
    · rw [rd' _ 1 3 _ (by omega_arith) (by omega_arith) (by omega_arith), rd' _ 1 2 _ (by omega_arith) (by omega_arith) (by omega_arith),
        Mem.readW_writeW_self64, v₃]
    · rw [rd' _ 2 3 _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64, v₅]
    · rw [Mem.readW_writeW_self64, v₇]

/-- 32 zero bytes, from four zero words. -/
theorem bytes32_zero {m : Mem} {p : Addr} (h : ∀ k < 4, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) :
    Spec.Ed25519.bytesAt m p 32 = Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.bytesAt, Spec.Ed25519.encodeLE]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have e : p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    rw [Offset.add_add]; congr 2; omega_arith
  rw [e, Proof.Ed25519.readW_byte64 m _ (Nat.mod_lt _ (by decide)), h _ (by omega_arith)]
  simp

end VG.Proof.Ed25519.PPC64LE.Whole
