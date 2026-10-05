import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.Chain`. -/
section

/-!
# Ed448 on AArch64: carry chains along registers

The value of a list of registers, lowest word first (`rv`), and a chain of
`adcs` (`adcs_ok`) or of an `adds` and `adcs` (`adds_ok`) along registers,
proven once by induction on the chain: the destinations' value plus the
carry out is the sum of the sources' values. A chain may write a register
it reads only when no later instruction of the chain reads or writes it
(`ChainOk`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem Keeps.refl (rs : List Reg) (s : VG.AArch64.State) : Keeps rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- The value of the registers `rs`, lowest first. -/
def rv (s : VG.AArch64.State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s rs

theorem pow64_succ (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem rv_lt (s : VG.AArch64.State) : ∀ rs : List Reg, VG.Proof.Ed448.AArch64.rv s rs < 2 ^ (64 * rs.length)
  | [] => by simp [VG.Proof.Ed448.AArch64.rv]
  | r :: rs => by
    have h1 := (s.gpr r).isLt
    have h2 := VG.Proof.Ed448.AArch64.rv_lt s rs
    rw [VG.Proof.Ed448.AArch64.rv, List.length_cons, VG.Proof.Ed448.AArch64.pow64_succ]
    generalize 2 ^ (64 * rs.length) = Q at h2 ⊢
    have : 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s rs + 2 ^ 64 ≤ 2 ^ 64 * Q := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
    omega

theorem rv_congr {s t : VG.AArch64.State} : ∀ {rs : List Reg}, (∀ r ∈ rs, t.gpr r = s.gpr r) → VG.Proof.Ed448.AArch64.rv t rs = VG.Proof.Ed448.AArch64.rv s rs
  | [], _ => rfl
  | r :: rs, h => by
    rw [VG.Proof.Ed448.AArch64.rv, VG.Proof.Ed448.AArch64.rv, h r List.mem_cons_self, VG.Proof.Ed448.AArch64.rv_congr fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]

theorem Keeps.rv_eq {rs : List Reg} {s t : VG.AArch64.State} (h : Keeps rs s t) {X : List Reg}
    (hX : ∀ r ∈ X, r ∉ rs) : VG.Proof.Ed448.AArch64.rv t X = VG.Proof.Ed448.AArch64.rv s X :=
  VG.Proof.Ed448.AArch64.rv_congr fun r hr => h.gpr r (hX r hr)

/-! ## Chains -/

/-- `adcs d, n, m` for each `(d, n, m)`. -/
def adcsOf (ts : List (Reg × Reg × Reg)) : List Instr := ts.map fun t => .adcs .x t.1 t.2.1 t.2.2

/-- No instruction of a chain reads or writes a register an earlier one wrote. -/
def ChainOk : List (Reg × Reg × Reg) → Bool
  | [] => true
  | t :: ts => ts.all (fun u => u.1 != t.1 && u.2.1 != t.1 && u.2.2 != t.1) && VG.Proof.Ed448.AArch64.ChainOk ts

def dsts (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.1)
def lhs (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.2.1)
def rhs (ts : List (Reg × Reg × Reg)) : List Reg := ts.map (·.2.2)

theorem addWithCarry_val (a b : BitVec 64) (c : Bool) :
    (a + b + BitVec.ofNat 64 c.toNat).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  simpa only [Ed25519.Word64.addCarry, Ed25519.Word64.carryOut] using
    Ed25519.Word64.addCarry_value a b c

theorem not_mem_map {ts : List (Reg × Reg × Reg)} {f : Reg × Reg × Reg → Reg} {d : Reg}
    (h : ∀ u ∈ ts, f u ≠ d) : ∀ r ∈ ts.map f, r ≠ d := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  exact h u hu

/-- A chain of `adcs`, from the carry `s.c`. -/
theorem adcs_ok : ∀ (ts : List (Reg × Reg × Reg)) (s : VG.AArch64.State), VG.Proof.Ed448.AArch64.ChainOk ts = true →
    WP isa (.block (VG.Proof.Ed448.AArch64.adcsOf ts)) s fun t =>
      VG.Proof.Ed448.AArch64.rv t (VG.Proof.Ed448.AArch64.dsts ts) + 2 ^ (64 * ts.length) * t.c.toNat = VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.lhs ts) + VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.rhs ts) + s.c.toNat ∧
      Keeps (VG.Proof.Ed448.AArch64.dsts ts) s t
  | [], s, _ => WP.block_nil ⟨by simp [VG.Proof.Ed448.AArch64.rv, VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs], Keeps.refl _ _⟩
  | (d, n, m) :: ts, s, h => by
    simp only [VG.Proof.Ed448.AArch64.ChainOk, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hd, hok⟩ := h
    rw [VG.Proof.Ed448.AArch64.adcsOf, List.map_cons, WP.block_cons_iff]
    let s1 := s.addWithCarry .x d (s.gpr n) (s.gpr m) s.c
    refine ⟨s1, by simp only [exec, read_x]; rfl, ?_⟩
    refine WP.mono (VG.Proof.Ed448.AArch64.adcs_ok ts s1 hok) fun t ⟨e, k⟩ => ?_
    have hdd : d ∉ VG.Proof.Ed448.AArch64.dsts ts := fun hm => VG.Proof.Ed448.AArch64.not_mem_map (fun u hu => (hd u hu).1.1) d hm rfl
    have g1 : t.gpr d = s1.gpr d := k.gpr d hdd
    have k1 : ∀ r, r ≠ d → s1.gpr r = s.gpr r := fun r hr => by
      simp only [s1, RegUpd.gpr_addWithCarry, hr, ite_false]
    have l1 : VG.Proof.Ed448.AArch64.rv s1 (VG.Proof.Ed448.AArch64.lhs ts) = VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.lhs ts) :=
      VG.Proof.Ed448.AArch64.rv_congr fun r hr => k1 r (VG.Proof.Ed448.AArch64.not_mem_map (fun u hu => (hd u hu).1.2) r hr)
    have r1 : VG.Proof.Ed448.AArch64.rv s1 (VG.Proof.Ed448.AArch64.rhs ts) = VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.rhs ts) :=
      VG.Proof.Ed448.AArch64.rv_congr fun r hr => k1 r (VG.Proof.Ed448.AArch64.not_mem_map (fun u hu => (hd u hu).2) r hr)
    have v1 := VG.Proof.Ed448.AArch64.addWithCarry_val (s.gpr n) (s.gpr m) s.c
    have d1 : s1.gpr d = s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat := by
      simp only [s1, RegUpd.gpr_addWithCarry, ite_true, BitVec.setWidth_eq]
    have c1 : s1.c = decide (2 ^ 64 ≤ (s.gpr n).toNat + (s.gpr m).toNat + s.c.toNat) := rfl
    rw [l1, r1, c1] at e
    refine ⟨?_, ⟨fun r hr => ?_, k.mem, k.rd, k.wr, k.sp⟩⟩
    · simp only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs, List.map_cons, VG.Proof.Ed448.AArch64.rv, List.length_cons]
      rw [g1, d1, VG.Proof.Ed448.AArch64.pow64_succ, Nat.mul_assoc]
      simp only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs] at e
      generalize 2 ^ (64 * ts.length) * t.c.toNat = Y at e ⊢
      generalize (s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat).toNat = D at v1 ⊢
      omega
    · simp only [VG.Proof.Ed448.AArch64.dsts, List.map_cons, List.mem_cons, not_or] at hr
      rw [k.gpr r hr.2, k1 r hr.1]

/-- A chain of an `adds` and `adcs`. -/
theorem adds_ok (d n m : Reg) (ts : List (Reg × Reg × Reg)) (s : VG.AArch64.State)
    (h : VG.Proof.Ed448.AArch64.ChainOk ((d, n, m) :: ts) = true) :
    WP isa (.block (.adds .x d n m :: VG.Proof.Ed448.AArch64.adcsOf ts)) s fun t =>
      VG.Proof.Ed448.AArch64.rv t (d :: VG.Proof.Ed448.AArch64.dsts ts) + 2 ^ (64 * (ts.length + 1)) * t.c.toNat =
        VG.Proof.Ed448.AArch64.rv s (n :: VG.Proof.Ed448.AArch64.lhs ts) + VG.Proof.Ed448.AArch64.rv s (m :: VG.Proof.Ed448.AArch64.rhs ts) ∧
      Keeps (d :: VG.Proof.Ed448.AArch64.dsts ts) s t := by
  have he : isa.exec (.adds .x d n m) s = isa.exec (.adcs .x d n m) { s with c := false } := rfl
  have e := VG.Proof.Ed448.AArch64.adcs_ok ((d, n, m) :: ts) { s with
                                               c := false } h
  rw [VG.Proof.Ed448.AArch64.adcsOf, List.map_cons, WP.block_cons_iff] at e
  rw [WP.block_cons_iff, he]
  obtain ⟨s1, h1, w⟩ := e
  refine ⟨s1, h1, WP.mono w fun t ⟨v, k⟩ => ⟨?_, ⟨fun r hr => k.gpr r hr, k.mem, k.rd, k.wr, k.sp⟩⟩⟩
  simpa only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs, List.map_cons, List.length_cons, Bool.toNat_false, Nat.add_zero,
    VG.Proof.Ed448.AArch64.rv_congr (s := s) (t := { s with
                                     c := false }) (fun _ _ => rfl)] using v

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.MemWords`. -/
section

/-!
# Ed448 on AArch64: words stored and loaded relative to a register

A list of `str` (`strs`) or `ldr` (`ldrs`) at offsets from one base
register, proven once by induction on the list: the stores write the words
in turn (`wrs`), each of which a later read finds if the offsets are
separate (`word_wrs`), and the loads read them.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs writeW_outside word_writeW_sep
  word_writeW_self)

/-- `str x_r, [b, #d]` for each `(r, d)`. -/
def strs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .str .x p.1 b p.2

/-- `ldr x_r, [b, #d]` for each `(r, d)`. -/
def ldrs (b : Reg) (ps : List (Reg × Nat)) : List Instr := ps.map fun p => .ldr .x p.1 b p.2

/-- The registers' values `g` written in turn at their offsets from `base`. -/
def wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) : List (Reg × Nat) → Mem
  | [] => m
  | p :: ps => VG.Proof.Ed448.AArch64.wrs (m.writeW (off base p.2) (g p.1)) base g ps

theorem strs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : VG.AArch64.State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions s.wr (off base p.2) 8) →
    WP isa (.block (VG.Proof.Ed448.AArch64.strs b ps)) s fun t => t = { s with
                                                        mem := VG.Proof.Ed448.AArch64.wrs s.mem base s.gpr ps }
  | [], s, _, _ => WP.block_nil rfl
  | p :: ps, s, hb, hw => by
    obtain ⟨h8, hl, hr⟩ := hw p List.mem_cons_self
    rw [VG.Proof.Ed448.AArch64.strs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_str_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    rw [hb]
    exact WP.mono (VG.Proof.Ed448.AArch64.strs_ok b ps _ hb fun q hq => hw q (List.mem_cons_of_mem _ hq)) fun t ht => ht

/-- Two words at offsets `d` and `e` do not overlap. -/
def Sep8 (d e : Nat) : Prop := d + 8 ≤ e ∨ e + 8 ≤ d

instance (d e : Nat) : Decidable (VG.Proof.Ed448.AArch64.Sep8 d e) := inferInstanceAs (Decidable (_ ∨ _))

theorem word_wrs_of_sep (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) {d : Nat}, (∀ p ∈ ps, VG.Proof.Ed448.AArch64.Sep8 p.2 d ∧ p.2 + 8 ≤ 2 ^ 64) →
      d + 8 ≤ 2 ^ 64 → word (VG.Proof.Ed448.AArch64.wrs m base g ps) base d = word m base d
  | [], _, _, _ => rfl
  | p :: ps, d, h, hd => by
    rw [VG.Proof.Ed448.AArch64.wrs, VG.Proof.Ed448.AArch64.word_wrs_of_sep _ base g ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) hd]
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact word_writeW_sep m base _ h1.symm h2 hd

theorem word_wrs (m : Mem) (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)), ps.Pairwise (fun p q => VG.Proof.Ed448.AArch64.Sep8 p.2 q.2) →
      (∀ p ∈ ps, p.2 + 8 ≤ 2 ^ 64) → ∀ p ∈ ps, word (VG.Proof.Ed448.AArch64.wrs m base g ps) base p.2 = g p.1
  | [], _, _, _, hp => nomatch hp
  | p :: ps, hs, hl, q, hq => by
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [VG.Proof.Ed448.AArch64.wrs, VG.Proof.Ed448.AArch64.word_wrs_of_sep _ base g ps (fun r hr => ⟨hs.1 r hr |>.symm, hl r
        (List.mem_cons_of_mem _ hr)⟩) (hl _ List.mem_cons_self)]
      exact word_writeW_self m base _ _
    · exact VG.Proof.Ed448.AArch64.word_wrs _ base g ps hs.2 (fun r hr => hl r (List.mem_cons_of_mem _ hr)) q hq
where
  symm {a b : Nat} (h : VG.Proof.Ed448.AArch64.Sep8 a b) : VG.Proof.Ed448.AArch64.Sep8 b a := h.symm

theorem wrs_outside (m : Mem) (base : Addr) (g : Reg → BitVec 64) {o n : Nat} (hn : o + n < 2 ^ 64) :
    ∀ (ps : List (Reg × Nat)), (∀ p ∈ ps, o ≤ p.2 ∧ p.2 + 8 ≤ o + n) →
      Outside base o n m (VG.Proof.Ed448.AArch64.wrs m base g ps)
  | [], _ => Outside.refl _ _ _ _
  | p :: ps, h => by
    obtain ⟨h1, h2⟩ := h p List.mem_cons_self
    exact ((writeW_outside m base (g p.1) (by omega)).mono h1 (by omega)).trans
      (VG.Proof.Ed448.AArch64.wrs_outside _ base g hn ps fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem wrs_frame {R : Region} {m : Mem} (base : Addr) (g : Reg → BitVec 64) :
    ∀ (ps : List (Reg × Nat)) (m' : Mem), Frame [R] m m' →
      (∀ p ∈ ps, R.Contains (off base p.2) 8) → Frame [R] m (VG.Proof.Ed448.AArch64.wrs m' base g ps)
  | [], _, h, _ => h
  | p :: ps, _, h, hc => VG.Proof.Ed448.AArch64.wrs_frame base g ps _
      (h.writeW (List.mem_singleton_self _) _ (hc p List.mem_cons_self))
      fun q hq => hc q (List.mem_cons_of_mem _ hq)

theorem ldrs_ok {base : Addr} (b : Reg) : ∀ (ps : List (Reg × Nat)) (s : VG.AArch64.State), s.gpr b = base →
    (∀ p ∈ ps, p.2 % 8 = 0 ∧ p.2 < 32768 ∧ InRegions (s.rd ++ s.wr) (off base p.2) 8 ∧ p.1 ≠ b) →
    (ps.map (·.1)).Nodup →
    WP isa (.block (VG.Proof.Ed448.AArch64.ldrs b ps)) s fun t =>
      (∀ p ∈ ps, t.gpr p.1 = word s.mem base p.2) ∧ Keeps (ps.map (·.1)) s t
  | [], s, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Keeps.refl _ _⟩
  | p :: ps, s, hb, hw, hnd => by
    obtain ⟨h8, hl, hr, hpb⟩ := hw p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [VG.Proof.Ed448.AArch64.ldrs, List.map_cons, WP.block_cons_iff]
    refine ⟨_, exec_ldr_x ⟨h8, hl⟩ (by rw [hb]; exact hr), ?_⟩
    let s1 := s.write .x p.1 (s.mem.readW (s.gpr b + BitVec.ofNat 64 p.2) 64)
    have k1 : ∀ r, r ≠ p.1 → s1.gpr r = s.gpr r := fun r hr =>
      RegUpd.gpr_write_of_ne s .x _ hr
    refine WP.mono (VG.Proof.Ed448.AArch64.ldrs_ok b ps s1 ((k1 b (Ne.symm hpb)).trans hb) (fun q hq => hw q
      (List.mem_cons_of_mem _ hq)) hnd.2) fun t ⟨ht, kt⟩ => ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [kt.gpr _ hnd.1, RegUpd.gpr_write_self, BitVec.setWidth_eq, hb]
      · exact ht q hq
    · refine ⟨fun r hr => ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩
      rw [List.map_cons, List.mem_cons, not_or] at hr
      rw [kt.gpr r hr.2, k1 r hr.1]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarWord`. -/
section

/-!
# Ed448 scalar arithmetic on AArch64: one word

`wordFold` turns the remainder `r < L` in `x5–x11` and the next word `w` in
`x4` into `n = l + h c` (in `N`) for `2^64 r + w = h 2^446 + l`
(`fold_words`), and `csub` reduces a value below `2L` modulo `L`. Each block
is checked against the numbers it computes, with the carry chains of
`Chain.lean`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x const64_ok)
open VG.Spec.Ed448 (L)

/-- The remainder: the seven words of `x5–x11`. -/
abbrev rem (s : State) : Nat := VG.Proof.Ed448.AArch64.rv s R

/-- The constants of `consts` in their registers. -/
structure Consts (s : State) : Prop where
  c0 : s.gpr C0 = c0
  c1 : s.gpr C1 = c1
  c2 : s.gpr C2 = c2
  c3 : s.gpr C3 = c3
  kt : s.gpr KT = 0xc000000000000000
  z : s.gpr Z = 0

/-- The registers the constants are in. -/
def constRegs : List Reg := [C0, C1, C2, C3, KT, Z]

theorem Consts.of_keeps {rs : List Reg} {s t : State} (h : VG.Proof.Ed448.AArch64.Consts s) (k : Keeps rs s t)
    (hr : ∀ r ∈ VG.Proof.Ed448.AArch64.constRegs, r ∉ rs) : VG.Proof.Ed448.AArch64.Consts t :=
  ⟨(k.gpr _ (hr _ (by decide))).trans h.c0, (k.gpr _ (hr _ (by decide))).trans h.c1,
    (k.gpr _ (hr _ (by decide))).trans h.c2, (k.gpr _ (hr _ (by decide))).trans h.c3,
    (k.gpr _ (hr _ (by decide))).trans h.kt, (k.gpr _ (hr _ (by decide))).trans h.z⟩

/-- The registers the loop's body changes. -/
def clob : List Reg :=
  [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20]

theorem constRegs_clob : ∀ r ∈ VG.Proof.Ed448.AArch64.constRegs, r ∉ VG.Proof.Ed448.AArch64.clob := by decide

theorem rem_eq (s : State) : VG.Proof.Ed448.AArch64.rem s = (s.gpr .x5).toNat + 2 ^ 64 * ((s.gpr .x6).toNat + 2 ^ 64 *
    ((s.gpr .x7).toNat + 2 ^ 64 * ((s.gpr .x8).toNat + 2 ^ 64 * ((s.gpr .x9).toNat + 2 ^ 64 *
    ((s.gpr .x10).toNat + 2 ^ 64 * (s.gpr .x11).toNat))))) := by
  simp only [VG.Proof.Ed448.AArch64.rem, VG.Proof.Ed448.AArch64.rv, R, Nat.mul_zero, Nat.add_zero]

/-! ## Folding a word in -/

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

theorem extr62 (lo hi : BitVec 64) (h : hi.toNat < 2 ^ 62) :
    ((hi ++ lo).extractLsb' 62 64).toNat = lo.toNat / 2 ^ 62 + 4 * hi.toNat := by
  have := lo.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem shl_shr2 (x : BitVec 64) : ((x <<< 2) >>> 2).toNat = x.toNat % 2 ^ 62 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- `foldSplit`: `h` into `x11`, `r₅ mod 2^62` into `x10`. -/
theorem foldSplit_ok (s : State) (h6 : (s.gpr .x11).toNat < 2 ^ 62) :
    WP isa (.block foldSplit) s fun t =>
      (t.gpr .x11).toNat = (s.gpr .x10).toNat / 2 ^ 62 + 4 * (s.gpr .x11).toNat ∧
      (t.gpr .x10).toNat = (s.gpr .x10).toNat % 2 ^ 62 ∧ Keeps [.x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [foldSplit, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 62 < Size.x.bits from by decide, show 2 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed448.AArch64.extr62 _ _ h6, VG.Proof.Ed448.AArch64.shl_shr2 _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mul_halves (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-- `foldMul`: the products of `h` by the words of `c`. -/
theorem foldMul_ok (s : State) :
    WP isa (.block VG.Impl.Ed448.AArch64.foldMul) s fun t =>
      (t.gpr .x12).toNat + 2 ^ 64 * (t.gpr .x16).toNat = (s.gpr .x11).toNat * (s.gpr C0).toNat ∧
      (t.gpr .x13).toNat + 2 ^ 64 * (t.gpr .x17).toNat = (s.gpr .x11).toNat * (s.gpr C1).toNat ∧
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x19).toNat = (s.gpr .x11).toNat * (s.gpr C2).toNat ∧
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x20).toNat = (s.gpr .x11).toNat * (s.gpr C3).toNat ∧
      Keeps [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Ed448.AArch64.foldMul, C0, C1, C2, C3, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed448.AArch64.mul_halves _ _, VG.Proof.Ed448.AArch64.mul_halves _ _, VG.Proof.Ed448.AArch64.mul_halves _ _, VG.Proof.Ed448.AArch64.mul_halves _ _,
    ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem foldProd_eq : foldProd = .adds .x .x13 .x13 .x16 ::
    VG.Proof.Ed448.AArch64.adcsOf [(.x14, .x14, .x17), (.x15, .x15, .x19), (.x20, .x20, Z)] := rfl

theorem c_words : c0.toNat + 2 ^ 64 * (c1.toNat + 2 ^ 64 * (c2.toNat + 2 ^ 64 * c3.toNat)) = VG.Proof.Ed448.cL := by
  decide

/-- `foldMul` and `foldProd`: `h c` in `x12–x15`, `x20`. -/
theorem foldMul_prod_ok (s : State) (hc : VG.Proof.Ed448.AArch64.Consts s) :
    WP isa (.block (VG.Impl.Ed448.AArch64.foldMul ++ foldProd)) s fun t =>
      (t.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv t [.x13, .x14, .x15, .x20] = (s.gpr .x11).toNat * VG.Proof.Ed448.cL ∧
      Keeps [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.foldMul_ok s) fun a ⟨e0, e1, e2, e3, ka⟩ => ?_
  rw [VG.Proof.Ed448.AArch64.foldProd_eq]
  refine WP.mono (VG.Proof.Ed448.AArch64.adds_ok _ _ _ _ a (by decide)) fun t ⟨et, kt⟩ => ?_
  have hz : a.gpr Z = 0 := (ka.gpr _ (by decide)).trans hc.z
  have h12 : t.gpr .x12 = a.gpr .x12 := kt.gpr _ (by decide)
  simp only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil, VG.Proof.Ed448.AArch64.rv,
    hz, VG.Proof.Ed448.AArch64.toNat_zero64, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul] at et
  simp only [VG.Proof.Ed448.AArch64.rv, Nat.mul_zero, Nat.add_zero]
  rw [h12]
  rw [hc.c0, hc.c1, hc.c2, hc.c3] at *
  have hb : (s.gpr .x11).toNat * VG.Proof.Ed448.cL < 2 ^ 64 * 2 ^ 224 :=
    Nat.mul_lt_mul'' (s.gpr .x11).isLt cL_lt
  have hcL : (s.gpr .x11).toNat * VG.Proof.Ed448.cL = (s.gpr .x11).toNat * c0.toNat + 2 ^ 64 *
      ((s.gpr .x11).toNat * c1.toNat + 2 ^ 64 * ((s.gpr .x11).toNat * c2.toNat + 2 ^ 64 *
        ((s.gpr .x11).toNat * c3.toNat))) := by
    rw [← VG.Proof.Ed448.AArch64.c_words]; grind
  have l3 : (a.gpr .x20).toNat < 2 ^ 32 := by
    have : (s.gpr .x11).toNat * c3.toNat < 2 ^ 64 * 2 ^ 32 :=
      Nat.mul_lt_mul'' (s.gpr .x11).isLt (by decide)
    have := (a.gpr .x15).isLt
    omega
  refine ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  have hc' := Bool.toNat_le t.c
  generalize (s.gpr .x11).toNat * c0.toNat = P0 at *
  generalize (s.gpr .x11).toNat * c1.toNat = P1 at *
  generalize (s.gpr .x11).toNat * c2.toNat = P2 at *
  generalize (s.gpr .x11).toNat * c3.toNat = P3 at *
  generalize (s.gpr .x11).toNat * VG.Proof.Ed448.cL = P at *
  have := (t.gpr .x13).isLt; have := (t.gpr .x14).isLt; have := (t.gpr .x15).isLt
  have := (t.gpr .x20).isLt
  omega

theorem foldAdd_eq : VG.Impl.Ed448.AArch64.foldAdd = .adds .x .x4 .x4 .x12 ::
    VG.Proof.Ed448.AArch64.adcsOf [(.x5, .x5, .x13), (.x6, .x6, .x14), (.x7, .x7, .x15), (.x8, .x8, .x20),
      (.x9, .x9, Z), (.x10, .x10, Z)] := rfl

/-- `foldAdd`: `x4–x10 += x12–x15, x20`, for a sum below `2^448`. -/
theorem foldAdd_ok (s : State) (hz : s.gpr Z = 0)
    (hlt : VG.Proof.Ed448.AArch64.rv s N + ((s.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s [.x13, .x14, .x15, .x20]) < 2 ^ 448) :
    WP isa (.block VG.Impl.Ed448.AArch64.foldAdd) s fun t =>
      VG.Proof.Ed448.AArch64.rv t N = VG.Proof.Ed448.AArch64.rv s N + ((s.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s [.x13, .x14, .x15, .x20]) ∧
      Keeps N s t := by
  rw [VG.Proof.Ed448.AArch64.foldAdd_eq]
  refine WP.mono (VG.Proof.Ed448.AArch64.adds_ok _ _ _ _ s (by decide)) fun t ⟨et, kt⟩ => ⟨?_, kt⟩
  have hc := Bool.toNat_le t.c
  simp only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul] at et
  have hp : VG.Proof.Ed448.AArch64.rv s [.x12, .x13, .x14, .x15, .x20, Z, Z] =
      (s.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s [.x13, .x14, .x15, .x20] := by
    simp only [VG.Proof.Ed448.AArch64.rv, hz, VG.Proof.Ed448.AArch64.toNat_zero64, Nat.mul_zero, Nat.add_zero]
  rw [hp] at et
  simp only [N] at hlt ⊢
  generalize VG.Proof.Ed448.AArch64.rv t [.x4, .x5, .x6, .x7, .x8, .x9, .x10] = T at et ⊢
  generalize VG.Proof.Ed448.AArch64.rv s [.x4, .x5, .x6, .x7, .x8, .x9, .x10] + ((s.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s [.x13, .x14, .x15, .x20]) = A at et hlt ⊢
  generalize (2 : Nat) ^ 448 = M at et hlt
  rcases Nat.lt_or_ge t.c.toNat 1 with h | h
  · obtain h0 : t.c.toNat = 0 := by omega
    rw [h0, Nat.mul_zero, Nat.add_zero] at et
    exact et
  · have := Nat.mul_le_mul_left M h
    omega

/-- The registers `wordFold` changes. -/
def foldClob : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20]

/-- `wordFold`: from the remainder `r < L` and the next word `w` in `x4`, a
value below `2L` congruent to `2^64 r + w`. -/
theorem wordFold_ok (s : State) (hc : VG.Proof.Ed448.AArch64.Consts s) (hr : VG.Proof.Ed448.AArch64.rem s < VG.Spec.Ed448.L) :
    WP isa (.block VG.Impl.Ed448.AArch64.wordFold) s fun t => VG.Proof.Ed448.AArch64.rv t N < 2 * VG.Spec.Ed448.L ∧
      VG.Proof.Ed448.AArch64.rv t N % VG.Spec.Ed448.L = ((s.gpr .x4).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rem s) % VG.Spec.Ed448.L ∧ Keeps VG.Proof.Ed448.AArch64.foldClob s t := by
  have hw := (s.gpr .x4).isLt
  have h0 := (s.gpr .x5).isLt; have h1 := (s.gpr .x6).isLt; have h2 := (s.gpr .x7).isLt
  have h3 := (s.gpr .x8).isLt; have h4 := (s.gpr .x9).isLt; have h5 := (s.gpr .x10).isLt
  have h6 := (s.gpr .x11).isLt
  rw [VG.Proof.Ed448.AArch64.rem_eq] at hr
  obtain ⟨h6', hh, hlt, hmod⟩ := fold_words _ _ _ _ _ _ _ _ hw h0 h1 h2 h3 h4 h5 h6 hr
  simp only [VG.Impl.Ed448.AArch64.wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.foldSplit_ok s h6') fun a ⟨a11, a10, ka⟩ => ?_
  have hca : VG.Proof.Ed448.AArch64.Consts a := hc.of_keeps ka (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.foldMul_prod_ok a hca) fun b ⟨eb, kb⟩ => ?_
  have hcb : VG.Proof.Ed448.AArch64.Consts b := hca.of_keeps kb (by decide)
  have nb : VG.Proof.Ed448.AArch64.rv b N = (s.gpr .x4).toNat + 2 ^ 64 * ((s.gpr .x5).toNat + 2 ^ 64 *
      ((s.gpr .x6).toNat + 2 ^ 64 * ((s.gpr .x7).toNat + 2 ^ 64 * ((s.gpr .x8).toNat +
      2 ^ 64 * ((s.gpr .x9).toNat + 2 ^ 64 * ((s.gpr .x10).toNat % 2 ^ 62)))))) := by
    simp only [N, VG.Proof.Ed448.AArch64.rv, Nat.mul_zero, Nat.add_zero]
    rw [kb.gpr .x4 (by decide), kb.gpr .x5 (by decide), kb.gpr .x6 (by decide),
      kb.gpr .x7 (by decide), kb.gpr .x8 (by decide), kb.gpr .x9 (by decide),
      kb.gpr .x10 (by decide), ka.gpr .x4 (by decide), ka.gpr .x5 (by decide),
      ka.gpr .x6 (by decide), ka.gpr .x7 (by decide), ka.gpr .x8 (by decide),
      ka.gpr .x9 (by decide), a10]
  rw [a11] at eb
  have hb : VG.Proof.Ed448.AArch64.rv b N + ((b.gpr .x12).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv b [.x13, .x14, .x15, .x20]) < 2 ^ 448 := by
    have : 2 * VG.Spec.Ed448.L < 2 ^ 448 := by decide +kernel
    rw [nb, eb]; exact Nat.lt_trans hlt this
  refine WP.mono (VG.Proof.Ed448.AArch64.foldAdd_ok b hcb.z hb) fun t ⟨et, kt⟩ => ?_
  rw [et, nb, eb]
  refine ⟨hlt, ?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [hmod, VG.Proof.Ed448.AArch64.rem_eq]

/-! ## The conditional subtraction -/

theorem csubAdd_eq : csubAdd = .adds .x .x12 .x4 C0 ::
    VG.Proof.Ed448.AArch64.adcsOf [(.x13, .x5, C1), (.x14, .x6, C2), (.x15, .x7, C3), (.x16, .x8, Z), (.x17, .x9, Z),
      (.x19, .x10, KT)] := rfl

theorem k_words : c0.toNat + 2 ^ 64 * (c1.toNat + 2 ^ 64 * (c2.toNat + 2 ^ 64 * (c3.toNat +
    2 ^ 64 * (0 + 2 ^ 64 * (0 + 2 ^ 64 * (0xc000000000000000 : BitVec 64).toNat))))) =
    2 ^ 448 - VG.Spec.Ed448.L := by decide +kernel

/-- `csubAdd`: `S = N + K`, with the carry out of 448 bits. -/
theorem csubAdd_ok (s : State) (hc : VG.Proof.Ed448.AArch64.Consts s) :
    WP isa (.block csubAdd) s fun t =>
      VG.Proof.Ed448.AArch64.rv t S + 2 ^ 448 * t.c.toNat = VG.Proof.Ed448.AArch64.rv s N + (2 ^ 448 - VG.Spec.Ed448.L) ∧ Keeps S s t := by
  rw [VG.Proof.Ed448.AArch64.csubAdd_eq]
  refine WP.mono (VG.Proof.Ed448.AArch64.adds_ok _ _ _ _ s (by decide)) fun t ⟨et, kt⟩ => ⟨?_, kt⟩
  simp only [VG.Proof.Ed448.AArch64.dsts, VG.Proof.Ed448.AArch64.lhs, VG.Proof.Ed448.AArch64.rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul] at et
  rw [← VG.Proof.Ed448.AArch64.k_words]
  simp only [S, N, VG.Proof.Ed448.AArch64.rv, Nat.mul_zero, Nat.add_zero] at et ⊢
  rw [hc.c0, hc.c1, hc.c2, hc.c3, hc.kt, hc.z, VG.Proof.Ed448.AArch64.toNat_zero64] at et
  exact et

def mask (c : Bool) : BitVec 64 := if c then 0 else -1

theorem sel_mask (c : Bool) (n s : BitVec 64) : s ^^^ ((n ^^^ s) &&& VG.Proof.Ed448.AArch64.mask c) = if c then s else n := by
  cases c
  · simp only [VG.Proof.Ed448.AArch64.mask, Bool.false_eq_true, ite_false]
    rw [show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, BitVec.xor_comm n s,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [VG.Proof.Ed448.AArch64.mask, ite_true]
    rw [show (n ^^^ s) &&& (0 : BitVec 64) = 0#64 from BitVec.and_zero, BitVec.xor_zero]

theorem sbcs_mask (c : Bool) :
    (0 : BitVec 64) + ~~~(0 : BitVec 64) + BitVec.ofNat 64 c.toNat = VG.Proof.Ed448.AArch64.mask c := by
  cases c <;> decide

/-- The mask, then the selection: `R` from `N` (without a carry) or `S`. -/
theorem csubSel_ok (s : State) (hz : s.gpr Z = 0) :
    WP isa (.block (.sbcs .x .x20 Z Z :: selTriples.flatMap fun (r, n, s) => sel r n s)) s
      fun t => VG.Proof.Ed448.AArch64.rem t = (if s.c then VG.Proof.Ed448.AArch64.rv s S else VG.Proof.Ed448.AArch64.rv s N) ∧
        Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x20] s t := by
  apply WP.of_runBlock
  simp only [selTriples, sel, Z, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  simp only [Z] at hz
  simp only [hz, VG.Proof.Ed448.AArch64.sbcs_mask]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · cases s.c <;> simp only [VG.Proof.Ed448.AArch64.rem, R, S, N, VG.Proof.Ed448.AArch64.rv, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, VG.Proof.Ed448.AArch64.sel_mask, Bool.false_eq_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- `csub`: `N` (below `2L`) modulo `L` into `R`. -/
theorem csub_ok (s : State) (hc : VG.Proof.Ed448.AArch64.Consts s) (hx : VG.Proof.Ed448.AArch64.rv s N < 2 * VG.Spec.Ed448.L) :
    WP isa (.block csub) s fun t => VG.Proof.Ed448.AArch64.rem t = VG.Proof.Ed448.AArch64.rv s N % VG.Spec.Ed448.L ∧ Keeps VG.Proof.Ed448.AArch64.foldClob s t := by
  rw [csub, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.csubAdd_ok s hc) fun a ⟨ea, ka⟩ => ?_
  have hza : a.gpr Z = 0 := (ka.gpr _ (by decide)).trans hc.z
  refine WP.mono (VG.Proof.Ed448.AArch64.csubSel_ok a hza) fun t ⟨et, kt⟩ => ⟨?_, (ka.mono (by decide)).trans
    (kt.mono (by decide))⟩
  have na : VG.Proof.Ed448.AArch64.rv a N = VG.Proof.Ed448.AArch64.rv s N := Keeps.rv_eq ka (by decide)
  have hlt := VG.Proof.Ed448.AArch64.rv_lt a S
  rw [na] at et
  have h2L : 2 * VG.Spec.Ed448.L ≤ 2 ^ 448 := by decide +kernel
  rw [et]
  simp only [S, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at hlt
  exact csub_nat h2L hx hlt ea

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop`. -/
section

/-!
# Ed448 scalar arithmetic on AArch64: the loop over the words

`scalarLoop` consumes the words of an input of `8n + t` bytes at `x1` from
the top, below the `t` bytes the remainder starts from: the invariant is the
value modulo `L` of the consumed top bytes. The body writes no memory.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Spec.Ed448 (L bytesAt decodeLE)

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .x3 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block VG.Impl.Ed448.AArch64.wordRead) s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .x4 = s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.x3, .x4] s t := by
  have hn : s.gpr .x3 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [VG.Impl.Ed448.AArch64.wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (8 : Nat) < 4096 from by decide, show (0 : Nat) % 8 = 0 from rfl,
    show (0 : Nat) < 4096 * 8 from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

theorem scalarWord_eq : VG.Impl.Ed448.AArch64.scalarWord = VG.Impl.Ed448.AArch64.wordRead ++ (VG.Impl.Ed448.AArch64.wordFold ++ csub) := by
  simp only [VG.Impl.Ed448.AArch64.scalarWord, List.append_assoc]

/-- One word: read, folded in, reduced. -/
theorem scalarWord_ok (s : State) (hc : VG.Proof.Ed448.AArch64.Consts s) (k : Nat)
    (hb : s.gpr .x3 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hv : VG.Proof.Ed448.AArch64.rem s < VG.Spec.Ed448.L) :
    WP isa (.block VG.Impl.Ed448.AArch64.scalarWord) s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (8 * k) ∧
      VG.Proof.Ed448.AArch64.rem t = ((s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rem s) % VG.Spec.Ed448.L ∧
      Keeps VG.Proof.Ed448.AArch64.clob s t := by
  rw [VG.Proof.Ed448.AArch64.scalarWord_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : VG.Proof.Ed448.AArch64.rem a = VG.Proof.Ed448.AArch64.rem s := Keeps.rv_eq ka (by decide)
  have hca : VG.Proof.Ed448.AArch64.Consts a := hc.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.wordFold_ok a hca (by rw [av]; exact hv)) fun b ⟨b2, bm, kb⟩ => ?_
  have hcb : VG.Proof.Ed448.AArch64.Consts b := hca.of_keeps kb (by decide)
  refine WP.mono (VG.Proof.Ed448.AArch64.csub_ok b hcb b2) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, ?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr _ (by decide), kb.gpr _ (by decide)]; exact ab
  · rw [tv, bm, ax, av]

theorem counter_test : ∀ n < 17, (BitVec.ofNat 64 (8 * n) != 0) = decide (n ≠ 0) := by decide

/-- The loop's invariant, after `n` words are left: the remainder is that of
the bytes from word `n` up, of the `len` bytes at `x1`. -/
structure LoopInv (len : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  pos : 0 < n
  bound : 8 * n ≤ len
  counter : s.gpr .x3 = BitVec.ofNat 64 (8 * n)
  value : VG.Proof.Ed448.AArch64.rem s = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * n)) (len - 8 * n)) % VG.Spec.Ed448.L
  keeps : Keeps VG.Proof.Ed448.AArch64.clob s₀ s

/-- The loop, from `n₀ ≥ 1` words left, with the remainder of the bytes above
them: the remainder of all `len` bytes. -/
theorem scalarLoop_ok (s₀ : State) (hc : VG.Proof.Ed448.AArch64.Consts s₀) {len n₀ : Nat} (hn : n₀ < 17)
    (hi : VG.Proof.Ed448.AArch64.LoopInv len s₀ n₀ s₀)
    (hr : ∀ k < n₀, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa scalarLoop s₀ fun t =>
      VG.Proof.Ed448.AArch64.rem t = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (s₀.gpr .x1) len) % VG.Spec.Ed448.L ∧ Keeps VG.Proof.Ed448.AArch64.clob s₀ t := by
  apply WP.loop (fun n s => n ≤ n₀ ∧ VG.Proof.Ed448.AArch64.LoopInv len s₀ n s) (n := n₀)
  · intro n s ⟨hnn, hi⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.pos; omega : n ≠ 0)
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hcs : VG.Proof.Ed448.AArch64.Consts s := hc.of_keeps hi.keeps VG.Proof.Ed448.AArch64.constRegs_clob
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k (by omega)
    have hb := hi.bound
    have hv : VG.Proof.Ed448.AArch64.rem s < VG.Spec.Ed448.L := by rw [hi.value]; exact Nat.mod_lt _ L_pos
    refine WP.mono (VG.Proof.Ed448.AArch64.scalarWord_ok s hcs k hi.counter hread hv) fun t ⟨tb, tv, tk⟩ => ?_
    have kt := hi.keeps.trans tk
    have vt : VG.Proof.Ed448.AArch64.rem t =
        VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) % VG.Spec.Ed448.L := by
      rw [tv, hp, hi.keeps.mem, hi.value, VG.Proof.Ed448.words_step _ _ len k hb, Nat.mul_comm (2 ^ 64),
        Nat.add_comm, VG.Proof.Ed448.mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, tb, VG.Proof.Ed448.AArch64.counter_test 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, read_x, tb, VG.Proof.Ed448.AArch64.counter_test k (by omega), decide_eq_true hk0],
        k, by omega, by omega, ⟨by omega, by omega, tb, vt, kt⟩⟩
  · exact ⟨Nat.le_refl _, hi⟩

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarIO`. -/
section

/-!
# Ed448 scalar arithmetic on AArch64: entry and exit

The callee-saved registers saved in the working space and restored, the
constants set up, the remainder of the top bytes of a 114-byte input, and
the remainder written out as 57 bytes.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x const64_ok word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The callee-saved registers -/

/-- The callee-saved registers `g` in the working space at `base`. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, word m base p.2 = g p.1

theorem saved_ok : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 64 := by decide

theorem saved_sep : saved.Pairwise (fun p q => VG.Proof.Ed448.AArch64.Sep8 p.2 q.2) := by decide

theorem saveRegs_ok {s : State} {base : Addr} (b : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveRegs b)) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 64 s.mem t.mem ∧ VG.Proof.Ed448.AArch64.Saved base s.gpr t.mem := by
  refine WP.mono (VG.Proof.Ed448.AArch64.strs_ok b saved s hb fun p hp => ?_) fun t ht => ?_
  · obtain ⟨h8, hl⟩ := VG.Proof.Ed448.AArch64.saved_ok p hp
    exact ⟨h8, by omega, _, hw, contains_sc (by omega)⟩
  · subst ht
    refine ⟨rfl, rfl, rfl, rfl,
      VG.Proof.Ed448.AArch64.wrs_outside _ _ _ (by omega) _ fun p hp => ⟨Nat.zero_le _, (VG.Proof.Ed448.AArch64.saved_ok p hp).2⟩,
      fun p hp => VG.Proof.Ed448.AArch64.word_wrs _ _ _ _ VG.Proof.Ed448.AArch64.saved_sep (fun q hq => by have := (VG.Proof.Ed448.AArch64.saved_ok q hq).2; omega) p hp⟩

/-- The registers `saved` holds. -/
def savedRegs : List Reg := saved.map (·.1)

theorem restoreRegs_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : VG.Proof.Ed448.AArch64.Saved base g s.mem) :
    WP isa (.block restoreRegs) s fun t =>
      (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧ Keeps VG.Proof.Ed448.AArch64.savedRegs s t := by
  refine WP.mono (VG.Proof.Ed448.AArch64.ldrs_ok .x2 saved s hb (fun p hp => ?_) (by decide)) fun t ⟨ht, kt⟩ =>
    ⟨fun p hp => (ht p hp).trans (hsv p hp), kt⟩
  obtain ⟨h8, hl⟩ := VG.Proof.Ed448.AArch64.saved_ok p hp
  exact ⟨h8, by omega, ⟨_, List.mem_append_right _ hw, contains_sc (by omega)⟩,
    (by decide : ∀ p ∈ saved, p.1 ≠ .x2) p hp⟩

/-! ## The constants -/

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t => VG.Proof.Ed448.AArch64.Consts t ∧ Keeps VG.Proof.Ed448.AArch64.constRegs s t := by
  simp only [consts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s C0 c0) fun a ⟨a0, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a C1 c1) fun b ⟨b1, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b C2 c2) fun c ⟨c2', kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok c C3 c3) fun d ⟨d3, kd⟩ => ?_
  apply WP.of_runBlock
  simp only [KT, Z, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [C0, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide)]; exact a0
  · simp only [C1, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide)]; exact b1
  · simp only [C2, RegUpd.gpr_write, reduceCtorEq, ite_false]
    rw [kd.gpr _ (by decide)]; exact c2'
  · simp only [C3, RegUpd.gpr_write, reduceCtorEq, ite_false]; exact d3
  · simp only [KT, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [Z, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [VG.Proof.Ed448.AArch64.constRegs, C0, C1, C2, C3, KT, Z, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    rw [kd.gpr _ (by simp [C3, hr.2.2.2.1]), kc.gpr _ (by simp [C2, hr.2.2.1]),
      kb.gpr _ (by simp [C1, hr.2.1]), ka.gpr _ (by simp [C0, hr.1])]
  · exact kd.mem.trans (kc.mem.trans (kb.mem.trans ka.mem))
  · exact kd.rd.trans (kc.rd.trans (kb.rd.trans ka.rd))
  · exact kd.wr.trans (kc.wr.trans (kb.wr.trans ka.wr))
  · exact kd.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))

/-! ## The top bytes -/

theorem toNat_byte (b : Byte) : ((b.setWidth 32).setWidth 64).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

theorem decode_two (m : Mem) (p : Addr) :
    VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt m p 2) = (m p).toNat + 256 * (m (p + 1)).toNat := by
  simp only [VG.Spec.Ed448.bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, VG.Spec.Ed448.decodeLE, BitVec.add_zero, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The remainder of the top two bytes of a 114-byte input. -/
theorem init114_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 112) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 113) 1) :
    WP isa (.block init114) s fun t =>
      VG.Proof.Ed448.AArch64.rem t = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 112) 2) ∧
      t.gpr .x3 = BitVec.ofNat 64 112 ∧
      Keeps [.x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [init114, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (112 : Nat) % 1 = 0 from rfl,
    show (112 : Nat) < 4096 * 1 from by decide, show (113 : Nat) < 4096 * 1 from by decide,
    and_self, h0, h1, show 8 < Size.x.bits from by decide, show 16 * 0 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [VG.Proof.Ed448.AArch64.decode_two, show s.gpr .x1 + BitVec.ofNat 64 112 + 1 = s.gpr .x1 + BitVec.ofNat 64 113 by
      rw [BitVec.add_assoc]; rfl]
    simp only [VG.Proof.Ed448.AArch64.rem, VG.Proof.Ed448.AArch64.rv, R, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    have b0 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 112)).isLt
    have b1 := (s.mem (s.gpr .x1 + BitVec.ofNat 64 113)).isLt
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, VG.Proof.Ed448.AArch64.toNat_byte, VG.Proof.Ed448.AArch64.toNat_byte, Nat.shiftLeft_eq]
    have z : (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0)).toNat = 0 := by decide
    rw [Ed25519.AArch64.read_byte, Ed25519.AArch64.read_byte, z]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## The result -/

theorem word_write_byte (m : Mem) (q : Addr) {d e : Nat} (h : d + 8 ≤ e) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) : word (m.write (off q e) 1 v) q d = word m q d := by
  simp only [word, Mem.readW]
  rw [Mem.read_write_sep (Offset.sep q (Or.inl h) (by omega) (by omega)) (by decide)]

theorem readW_write_byte (m : Mem) (q : Addr) {d e : Nat} (h : d + 8 ≤ e) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) :
    (m.write (q + BitVec.ofNat 64 e) 1 v).readW (q + BitVec.ofNat 64 d) 64 =
      m.readW (q + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Offset.sep q (Or.inl h) (by omega) (by omega)) (by decide)]

theorem write_byte_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  simp only [Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_lt_one, ite_true, Nat.mul_zero]
  exact BitVec.extractLsb'_eq_self

theorem toNat_zero8 : (0 : BitVec (8 * 1)).toNat = 0 := rfl

theorem outWords_ok : ∀ p ∈ outWords, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 56 := by decide

theorem outWords_sep : outWords.Pairwise (fun p q => VG.Proof.Ed448.AArch64.Sep8 p.2 q.2) := by decide

/-- The zero byte at `q + 56`. -/
theorem zeroByte_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q)
    (hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block [.movz .x .x12 0 0, .strb .x12 .x0 56]) s fun t =>
      t.mem = s.mem.write (q + BitVec.ofNat 64 56) 1 0 ∧ (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read, hq,
    show 16 * 0 < Size.x.bits from by decide, show (56 : Nat) % 1 = 0 from rfl,
    show (56 : Nat) < 4096 * 1 from by decide, and_self, RegUpd.wr_write, RegUpd.gpr_write,
    RegUpd.mem_write, ite_true, ite_false, reduceCtorEq, hb, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨congrArg _ (by decide), fun r hr => by simp only [hr, ite_false], rfl, trivial, rfl⟩

/-- The remainder to the 57 bytes at `q`. -/
theorem outStore_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block (outWords.map (fun p => .str .x p.1 .x0 p.2) ++
        ([.movz .x .x12 0 0, .strb .x12 .x0 56] : List Instr))) s fun t =>
      VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt t.mem q 57) = VG.Proof.Ed448.AArch64.rem s ∧ Frame [⟨q, 57⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.strs_ok .x0 outWords s hq fun p hp => ?_) fun a ha => ?_
  · obtain ⟨h8, hl⟩ := VG.Proof.Ed448.AArch64.outWords_ok p hp
    exact ⟨h8, by omega, _, hw, Offset.contains_base q (by omega) (by omega)⟩
  subst ha
  have hb : InRegions s.wr (q + BitVec.ofNat 64 56) 1 :=
    ⟨_, hw, Offset.contains_base q (d := 56) (n := 1) (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.Ed448.AArch64.zeroByte_ok hq hb) fun t ⟨mt, gt, rdt, wrt, spt⟩ => ?_
  refine ⟨?_, ?_, gt, rdt, wrt, spt⟩
  · rw [mt, decode57]
    have hw' : ∀ p ∈ outWords, word (VG.Proof.Ed448.AArch64.wrs s.mem q s.gpr outWords) q p.2 = s.gpr p.1 :=
      VG.Proof.Ed448.AArch64.word_wrs _ _ _ _ VG.Proof.Ed448.AArch64.outWords_sep fun p hp => by have := (VG.Proof.Ed448.AArch64.outWords_ok p hp).2; omega
    have w0 := hw' (.x5, 0) (by decide)
    have w1 := hw' (.x6, 8) (by decide)
    have w2 := hw' (.x7, 16) (by decide)
    have w3 := hw' (.x8, 24) (by decide)
    have w4 := hw' (.x9, 32) (by decide)
    have w5 := hw' (.x10, 40) (by decide)
    have w6 := hw' (.x11, 48) (by decide)
    simp (disch := decide) only [VG.Proof.Ed448.AArch64.readW_write_byte, VG.Proof.Ed448.AArch64.write_byte_self, w0, w1, w2, w3, w4, w5, w6,
      VG.Proof.Ed448.AArch64.toNat_zero8, Nat.mul_zero, Nat.add_zero]
    rw [VG.Proof.Ed448.AArch64.rem_eq]
  · rw [mt]
    exact (VG.Proof.Ed448.AArch64.wrs_frame q s.gpr outWords s.mem (Frame.refl _ _) fun p hp =>
      Offset.contains_base q (by have := (VG.Proof.Ed448.AArch64.outWords_ok p hp).2; omega)
        (by have := (VG.Proof.Ed448.AArch64.outWords_ok p hp).2; omega)).write
      (List.mem_singleton_self _) _ (Offset.contains_base q (d := 56) (n := 1) (by omega) (by omega))

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarOperands`. -/
section

/-!
# Ed448 scalar multiply-add on AArch64: the operands

Each 57-byte input is copied to the working space as eight words, the top
one its last byte (`copy57_ok`), without reading past it; the values of
words in the working space are `mv`. The inputs are outside the working
space, so the copies leave them unchanged.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs contains_sc writeW_outside
  word_writeW_self)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- The value of the `n` words at `base + o`, lowest first. -/
def mv (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | o, n + 1 => (word m base o).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.mv m base (o + 8) n

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n)
    (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

/-- A word of a buffer disjoint from the working space, after writes inside it. -/
theorem readW_far {base p : Addr} {n o k d : Nat} {m m' : Mem} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hdn : d + 8 ≤ n)
    (hn : n ≤ 2 ^ 64) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  (Mem.readW_congr fun i hi => (h _ (Or.inr (by
    rw [Offset.add_add]; have := VG.Proof.Ed448.AArch64.far hd (i := d + i) (by omega) hn; omega))).symm).symm

/-- One word copied from `src + 8i` to `x4 + o + 8i`. -/
def copyPair (src : Reg) (o i : Nat) : List Instr :=
  [.ldr .x .x5 src (8 * i), .str .x .x5 .x4 (o + 8 * i)]

theorem copy57_eq (src : Reg) (o : Nat) : copy57 src o =
    (List.range 7).flatMap (VG.Proof.Ed448.AArch64.copyPair src o) ++
      ([.ldrb .x5 src 56, .str .x .x5 .x4 (o + 56)] : List Instr) := rfl

/-- What a copy keeps: all registers but `x5`, the permissions and the stack pointer. -/
structure CopyKeeps (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem CopyKeeps.trans {s t u : State} (h : VG.Proof.Ed448.AArch64.CopyKeeps s t) (k : VG.Proof.Ed448.AArch64.CopyKeeps t u) : VG.Proof.Ed448.AArch64.CopyKeeps s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

/-- The setting of a copy: the base of the working space in `x4`, the
source in `src`, outside it. -/
structure CopyPre (s : State) (base p : Addr) (src : Reg) (o : Nat) : Prop where
  x4 : s.gpr .x4 = base
  hsrc : s.gpr src = p
  src5 : src ≠ .x5
  src4 : src ≠ .x4
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  rd : (⟨p, 57⟩ : Region) ∈ s.rd ++ s.wr
  disj : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩
  o8 : o % 8 = 0
  olt : o + 64 ≤ 8192

theorem CopyPre.of_keeps {s t : State} {base p : Addr} {src : Reg} {o : Nat}
    (h : VG.Proof.Ed448.AArch64.CopyPre s base p src o) (k : VG.Proof.Ed448.AArch64.CopyKeeps s t) : VG.Proof.Ed448.AArch64.CopyPre t base p src o :=
  ⟨(k.gpr _ (by decide)).trans h.x4, (k.gpr _ h.src5).trans h.hsrc, h.src5, h.src4, k.wr ▸ h.wr,
    by rw [k.rd, k.wr]; exact h.rd, h.disj, h.o8, h.olt⟩

theorem copyPair_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : VG.Proof.Ed448.AArch64.CopyPre s base p src o)
    (i : Nat) (hi : i < 7) :
    WP isa (.block (VG.Proof.Ed448.AArch64.copyPair src o i)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i)) (s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64) ∧
      VG.Proof.Ed448.AArch64.CopyKeeps s t := by
  rw [VG.Proof.Ed448.AArch64.copyPair, WP.block_cons_iff]
  refine ⟨_, exec_ldr_x ⟨by omega, by omega⟩ (by
    rw [h.hsrc]; exact ⟨_, h.rd, Offset.contains_base p (by omega) (by omega)⟩), ?_⟩
  rw [WP.block_cons_iff]
  have hw : InRegions (s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).wr
      ((s.write .x .x5 (s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * i)) 64)).gpr .x4 +
        BitVec.ofNat 64 (o + 8 * i)) 8 := by
    rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (by decide), h.x4]
    exact ⟨_, h.wr, contains_sc (by have := h.olt; omega)⟩
  refine ⟨_, exec_str_x ⟨by have := h.o8; omega, by have := h.olt; omega⟩ hw, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩⟩
  simp only [RegUpd.mem_write, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _
    (show Reg.x4 ≠ .x5 by decide), BitVec.setWidth_eq, h.x4, h.hsrc]

/-- The first `n` words copied. -/
theorem copyWords_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : VG.Proof.Ed448.AArch64.CopyPre s base p src o) :
    ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap (VG.Proof.Ed448.AArch64.copyPair src o))) s fun t =>
      (∀ j < n, word t.mem base (o + 8 * j) = s.mem.readW (p + BitVec.ofNat 64 (8 * j)) 64) ∧
      Outside base o (8 * n) s.mem t.mem ∧ VG.Proof.Ed448.AArch64.CopyKeeps s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.copyWords_ok h n (by omega)) fun a ⟨wa, oa, ka⟩ => ?_
    have olt := h.olt
    refine WP.mono (VG.Proof.Ed448.AArch64.copyPair_ok (h.of_keeps ka) n (by omega)) fun t ⟨mt, kt⟩ => ?_
    have rp : a.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (p + BitVec.ofNat 64 (8 * n)) 64 :=
      VG.Proof.Ed448.AArch64.readW_far oa (by omega) h.disj (by omega) (by omega)
    refine ⟨fun j hj => ?_, ?_, ka.trans kt⟩
    · rw [mt, rp]
      rcases Nat.lt_or_ge j n with hj' | hj'
      · rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
        exact wa j hj'
      · obtain rfl : j = n := by omega
        exact word_writeW_self _ _ _ _
    · rw [mt]
      exact oa.mono (Nat.le_refl _) (by omega) |>.trans
        ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))

theorem mv8 (m : Mem) (base : Addr) (o : Nat) : VG.Proof.Ed448.AArch64.mv m base o 8 =
    (word m base o).toNat + 2 ^ 64 * ((word m base (o + 8)).toNat + 2 ^ 64 *
    ((word m base (o + 16)).toNat + 2 ^ 64 * ((word m base (o + 24)).toNat + 2 ^ 64 *
    ((word m base (o + 32)).toNat + 2 ^ 64 * ((word m base (o + 40)).toNat + 2 ^ 64 *
    ((word m base (o + 48)).toNat + 2 ^ 64 * (word m base (o + 56)).toNat)))))) := by
  simp only [VG.Proof.Ed448.AArch64.mv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

theorem toNat_byte64 (b : Byte) :
    (BitVec.setWidth (8 * 8) ((b.setWidth 32).setWidth 64)).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

/-- A 57-byte input copied as eight words. -/
theorem copy57_ok {s : State} {base p : Addr} {src : Reg} {o : Nat} (h : VG.Proof.Ed448.AArch64.CopyPre s base p src o) :
    WP isa (.block (copy57 src o)) s fun t =>
      VG.Proof.Ed448.AArch64.mv t.mem base o 8 = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem p 57) ∧ Outside base o 64 s.mem t.mem ∧
      VG.Proof.Ed448.AArch64.CopyKeeps s t := by
  rw [VG.Proof.Ed448.AArch64.copy57_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.copyWords_ok h 7 (Nat.le_refl _)) fun a ⟨wa, oa, ka⟩ => ?_
  have ha := h.of_keeps ka
  have olt := h.olt
  have o8 := h.o8
  have hb : InRegions (a.rd ++ a.wr) (a.gpr src + BitVec.ofNat 64 56) 1 := by
    rw [ha.hsrc]; exact ⟨_, ha.rd, Offset.contains_base p (d := 56) (n := 1) (by omega) (by omega)⟩
  have hw : InRegions a.wr (a.gpr .x4 + BitVec.ofNat 64 (o + 56)) 8 := by
    rw [ha.x4]; exact ⟨_, ha.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, read_x,
    Size.bytes, show (56 : Nat) % 1 = 0 from rfl, show (56 : Nat) < 4096 * 1 from by decide, and_self,
    hb, show (o + 56) % 8 = 0 by omega, show o + 56 < 4096 * 8 by omega, hw,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [ha.x4, ha.hsrc, Ed25519.AArch64.write64_eq_writeW]
  refine ⟨?_, oa.mono (Nat.le_refl _) (by omega) |>.trans
    ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)),
    ka.trans ⟨fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩⟩
  have byte : (a.mem.read (p + BitVec.ofNat 64 56) 1) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [Ed25519.AArch64.read_byte]
    exact oa _ (Or.inr (by have := VG.Proof.Ed448.AArch64.far h.disj (i := 56) (by omega) (by omega); omega))
  rw [VG.Proof.Ed448.AArch64.mv8, decode57]
  have w0 := wa 0 (by omega); have w1 := wa 1 (by omega); have w2 := wa 2 (by omega)
  have w3 := wa 3 (by omega); have w4 := wa 4 (by omega); have w5 := wa 5 (by omega)
  have w6 := wa 6 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at w0 w1 w2 w3 w4 w5 w6
  simp only [Ed25519.AArch64.word_writeW_self]
  rw [Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    Ed25519.AArch64.word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    w0, w1, w2, w3, w4, w5, w6, byte, VG.Proof.Ed448.AArch64.toNat_byte64]

theorem Outside.mv_eq {base : Addr} {o k : Nat} {m m' : Mem} (h : Outside base o k m m') :
    ∀ (n d : Nat), (d + 8 * n ≤ o ∨ o + k ≤ d) → d + 8 * n < 2 ^ 64 → VG.Proof.Ed448.AArch64.mv m' base d n = VG.Proof.Ed448.AArch64.mv m base d n
  | 0, _, _, _ => rfl
  | n + 1, d, hd, hl => by
    show (word m' base d).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.mv m' base (d + 8) n =
      (word m base d).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.mv m base (d + 8) n
    rw [Outside.mv_eq h n (d + 8) (by omega) (by omega), h.word (by omega) (by omega)]

/-- The bytes of a buffer disjoint from the working space, after writes
inside it only. -/
theorem bytesAt_outside {m m' : Mem} {p base : Addr} {n o k : Nat} (h : Outside base o k m m')
    (hk : o + k ≤ 8192) (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) (hn : n ≤ 2 ^ 64) :
    VG.Spec.Ed448.bytesAt m' p n = VG.Spec.Ed448.bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  exact h _ (Or.inr (by have := VG.Proof.Ed448.AArch64.far hd hi hn; omega))

/-- The operands: `k` then `r` at `XK`, `s` then one at `YS`. -/
theorem operands_ok {s : State} {base : Addr} (hb : s.gpr .x4 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hr : (⟨s.gpr .x1, 57⟩ : Region) ∈ s.rd ++ s.wr) (hk : (⟨s.gpr .x2, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hs : (⟨s.gpr .x3, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (dr : (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    (dk : (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    (ds : (⟨s.gpr .x3, 57⟩ : Region).Disjoint ⟨base, 8192⟩) :
    WP isa (.block operands) s fun t =>
      VG.Proof.Ed448.AArch64.mv t.mem base XK 8 = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) ∧
      VG.Proof.Ed448.AArch64.mv t.mem base (XK + 64) 8 = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) ∧
      VG.Proof.Ed448.AArch64.mv t.mem base YS 8 = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x3) 57) ∧
      word t.mem base (YS + 64) = 1 ∧ Outside base XK 200 s.mem t.mem ∧
      t.gpr .x2 = base ∧ (∀ r, r ∉ [Reg.x2, .x5] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [operands, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.copy57_ok ⟨hb, rfl, by decide, by decide, hw, hk, dk, by decide, by decide⟩)
    fun a ⟨va, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.copy57_ok ⟨(ka.gpr _ (by decide)).trans hb, (ka.gpr _ (by decide)), by decide,
    by decide, ka.wr ▸ hw, by rw [ka.rd, ka.wr]; exact hr, dr, by decide, by decide⟩)
    fun b ⟨vb, ob, kb⟩ => ?_
  rw [WP.block_append_iff]
  have kab := ka.trans kb
  refine WP.mono (VG.Proof.Ed448.AArch64.copy57_ok ⟨(kab.gpr _ (by decide)).trans hb, (kab.gpr _ (by decide)), by decide,
    by decide, kab.wr ▸ hw, by rw [kab.rd, kab.wr]; exact hs, ds, by decide, by decide⟩)
    fun c ⟨vc, oc, kc⟩ => ?_
  have kac := kab.trans kc
  have hwc : InRegions c.wr (c.gpr .x4 + BitVec.ofNat 64 (YS + 64)) 8 := by
    rw [kac.gpr _ (by decide), hb, kac.wr]; exact ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, read_x,
    Impl.Ed25519.AArch64.mov, Size.bytes, show (YS + 64) % 8 = 0 from rfl,
    show YS + 64 < 4096 * 8 from by decide, show (0 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hwc,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left']
  have x4c : c.gpr .x4 = base := (kac.gpr _ (by decide)).trans hb
  have one : BitVec.setWidth (8 * 8) (BitVec.setWidth 64
      (BitVec.setWidth Size.x.bits (1 : BitVec 16) <<< (16 * 0))) = (1 : BitVec 64) := by decide
  rw [x4c, Ed25519.AArch64.write64_eq_writeW, one]
  have ho : Outside base (YS + 64) 8 c.mem (c.mem.writeW (off base (YS + 64)) (1 : BitVec 64)) :=
    writeW_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_, by simp only [BitVec.add_zero, BitVec.setWidth_eq],
    fun r hr => ?_, kac.rd, kac.wr, by simp only [RegUpd.sp_write]; exact kac.sp⟩
  · rw [Outside.mv_eq ho 8 XK (by decide) (by decide), Outside.mv_eq oc 8 XK (by decide) (by decide),
      Outside.mv_eq ob 8 XK (by decide) (by decide), va]
  · rw [Outside.mv_eq ho 8 (XK + 64) (by decide) (by decide), Outside.mv_eq oc 8 (XK + 64) (by decide) (by decide), vb,
      VG.Proof.Ed448.AArch64.bytesAt_outside oa (by decide) dr (by decide)]
  · rw [Outside.mv_eq ho 8 YS (by decide) (by decide), vc, VG.Proof.Ed448.AArch64.bytesAt_outside ob (by decide) ds (by decide),
      VG.Proof.Ed448.AArch64.bytesAt_outside oa (by decide) ds (by decide)]
  · exact (((oa.mono (by decide) (by decide)).trans (ob.mono (by decide) (by decide))).trans
      (oc.mono (by decide) (by decide))).trans (ho.mono (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]
    exact kac.gpr r hr.2

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarColumns`. -/
section

/-!
# Ed448 scalar multiply-add on AArch64: product scanning

A term (`term_ok`): `x_i · y_j`, loaded from the working space, added to a
three-word accumulator; a column's terms (`terms_ok`), by induction on them;
and the sixteen columns (`columns_ok`), by induction on the columns, each
storing its low word at `ACC` and passing the rest of its accumulator on, in
`x5–x7` rotated. The columns of `r + k s` sum to it (`mulCols_sum`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs contains_sc writeW_outside
  word_writeW_self)

/-- The working space at `base`, in `x2`, with zero in `x26`. -/
structure Wk (s : State) (base : Addr) : Prop where
  x2 : s.gpr .x2 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  z : s.gpr .x26 = 0

theorem Wk.of_keeps {rs : List Reg} {s t : State} {base : Addr} (h : VG.Proof.Ed448.AArch64.Wk s base) (k : Keeps rs s t)
    (h2 : .x2 ∉ rs) (h26 : .x26 ∉ rs) : VG.Proof.Ed448.AArch64.Wk t base :=
  ⟨(k.gpr _ h2).trans h.x2, k.wr ▸ h.wr, (k.gpr _ h26).trans h.z⟩

/-- The `i`-th left and `j`-th right operand. -/
abbrev xw (m : Mem) (base : Addr) (i : Nat) : Nat := (word m base (XK + 8 * i)).toNat
abbrev yw (m : Mem) (base : Addr) (j : Nat) : Nat := (word m base (YS + 8 * j)).toNat

theorem umulh_eq (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := VG.Proof.Ed448.AArch64.mul_halves a b

/-- `term`: `a₀ a₁ a₂ += x_i · y_j`. -/
theorem term_ok {s : State} {base : Addr} {a0 a1 a2 : Reg} (hs : VG.Proof.Ed448.AArch64.Wk s base)
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) {i j : Nat} (hi : i < 16)
    (hj : j < 9) (hb : VG.Proof.Ed448.AArch64.rv s [a0, a1, a2] + VG.Proof.Ed448.AArch64.xw s.mem base i * VG.Proof.Ed448.AArch64.yw s.mem base j < 2 ^ 192) :
    WP isa (.block (term a0 a1 a2 i j)) s fun t =>
      VG.Proof.Ed448.AArch64.rv t [a0, a1, a2] = VG.Proof.Ed448.AArch64.rv s [a0, a1, a2] + VG.Proof.Ed448.AArch64.xw s.mem base i * VG.Proof.Ed448.AArch64.yw s.mem base j ∧
      Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0b, h0c, h0d, h0z, h0x⟩, ⟨h12, h1a, h1b, h1c, h1d, h1z, h1x⟩,
    ⟨h2a, h2b, h2c, h2d, h2z, h2x⟩, -⟩ := hd
  have l1 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [XK]; omega)⟩
  have l2 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [YS]; omega)⟩
  apply WP.of_runBlock
  simp only [term, Z, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (XK + 8 * i) % 8 = 0 by simp only [XK]; omega,
    show XK + 8 * i < 4096 * 8 by simp only [XK]; omega,
    show (YS + 8 * j) % 8 = 0 by simp only [YS]; omega,
    show YS + 8 * j < 4096 * 8 by simp only [YS]; omega, and_self, l1, l2,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.c_addWithCarry, BitVec.setWidth_eq, Ne.symm h01, Ne.symm h02, Ne.symm h12,
    h0a, h0b, h0c, h0d, h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d,
    Ne.symm h0d, Ne.symm h0z, Ne.symm h1z, hs.z,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [VG.Proof.Ed448.AArch64.rv, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, h01, h02, h12,
      Ne.symm h01, Ne.symm h02, Ne.symm h12, ite_true, ite_false, Nat.mul_zero, Nat.add_zero]
    have ex : VG.Proof.Ed448.AArch64.xw s.mem base i = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8).toNat := by
      simp only [VG.Proof.Ed448.AArch64.xw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    have ey : VG.Proof.Ed448.AArch64.yw s.mem base j = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8).toNat := by
      simp only [VG.Proof.Ed448.AArch64.yw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    rw [ex, ey] at hb ⊢
    simp only [VG.Proof.Ed448.AArch64.rv, Nat.mul_zero, Nat.add_zero] at hb
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 = x at hb ⊢
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 = y at hb ⊢
    have hp := VG.Proof.Ed448.AArch64.umulh_eq x y
    generalize x * y = lo at hp ⊢
    generalize BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) = hi at hp ⊢
    have v0 := VG.Proof.Ed448.AArch64.addWithCarry_val (s.gpr a0) lo false
    generalize decide (2 ^ 64 ≤ (s.gpr a0).toNat + lo.toNat + false.toNat) = c0 at v0 ⊢
    have v1 := VG.Proof.Ed448.AArch64.addWithCarry_val (s.gpr a1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr a1).toNat + hi.toNat + c0.toNat) = c1 at v1 ⊢
    have v2 : (s.gpr a2 + 0 + BitVec.ofNat 64 c1.toNat).toNat = ((s.gpr a2).toNat + c1.toNat) % 2 ^ 64 := by
      rw [show s.gpr a2 + 0 = s.gpr a2 from BitVec.add_zero _, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := Bool.toNat_le c1
      rw [Nat.mod_eq_of_lt (a := c1.toNat) (by omega)]
    rw [v2]
    have := (s.gpr a0).isLt; have := (s.gpr a1).isLt; have := (s.gpr a2).isLt
    have := Bool.toNat_le c0; have := Bool.toNat_le c1
    generalize (s.gpr a0 + lo + BitVec.ofNat 64 false.toNat).toNat = A0 at v0 ⊢
    simp only [Bool.toNat_false, Nat.add_zero] at v0
    generalize (s.gpr a1 + hi + BitVec.ofNat 64 c0.toNat).toNat = A1 at v1 ⊢
    generalize x.toNat * y.toNat = P at hp hb ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- The sum of a column's terms. -/
def colSum (xv yv : Nat → Nat) (ts : List (Nat × Nat)) : Nat := (ts.map fun t => xv t.1 * yv t.2).sum

theorem colSum_cons (xv yv : Nat → Nat) (t : Nat × Nat) (ts : List (Nat × Nat)) :
    VG.Proof.Ed448.AArch64.colSum xv yv (t :: ts) = xv t.1 * yv t.2 + VG.Proof.Ed448.AArch64.colSum xv yv ts := by
  simp [VG.Proof.Ed448.AArch64.colSum]

/-- A column's terms, by induction on them. -/
theorem terms_ok {base : Addr} {a0 a1 a2 : Reg}
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) :
    ∀ (ts : List (Nat × Nat)) (s : State), VG.Proof.Ed448.AArch64.Wk s base → (∀ t ∈ ts, t.1 < 16 ∧ t.2 < 9) →
      VG.Proof.Ed448.AArch64.rv s [a0, a1, a2] + VG.Proof.Ed448.AArch64.colSum (VG.Proof.Ed448.AArch64.xw s.mem base) (VG.Proof.Ed448.AArch64.yw s.mem base) ts < 2 ^ 192 →
      WP isa (.block (ts.flatMap fun t => term a0 a1 a2 t.1 t.2)) s fun s' =>
        VG.Proof.Ed448.AArch64.rv s' [a0, a1, a2] = VG.Proof.Ed448.AArch64.rv s [a0, a1, a2] + VG.Proof.Ed448.AArch64.colSum (VG.Proof.Ed448.AArch64.xw s.mem base) (VG.Proof.Ed448.AArch64.yw s.mem base) ts ∧
        Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [VG.Proof.Ed448.AArch64.colSum], Keeps.refl _ _⟩
  | t :: ts, s, hs, hc, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    rw [VG.Proof.Ed448.AArch64.colSum_cons] at hb
    have hct := hc t List.mem_cons_self
    refine WP.mono (VG.Proof.Ed448.AArch64.term_ok hs hd hct.1 hct.2 (by omega)) fun s1 ⟨e1, k1⟩ => ?_
    have hn := hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨-, -, -, -, -, -, h0z, h0x⟩, ⟨-, -, -, -, -, h1z, h1x⟩, ⟨-, -, -, -, h2z, h2x⟩, -⟩ := hn
    have hs1 : VG.Proof.Ed448.AArch64.Wk s1 base := hs.of_keeps k1
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0x, Ne.symm h1x, Ne.symm h2x⟩)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0z, Ne.symm h1z, Ne.symm h2z⟩)
    have m1 : s1.mem = s.mem := k1.mem
    refine WP.mono (VG.Proof.Ed448.AArch64.terms_ok hd ts s1 hs1 (fun t' ht' => hc t' (List.mem_cons_of_mem _ ht'))
      (by rw [e1, m1]; omega)) fun s2 ⟨e2, k2⟩ => ⟨?_, k1.trans k2⟩
    rw [e2, e1, VG.Proof.Ed448.AArch64.colSum_cons, m1]
    omega

/-- The registers a product's columns change. -/
def colX : List Reg := [.x5, .x6, .x7, .x12, .x13, .x14, .x15]

/-- The accumulator of column `k`. -/
def acc (k : Nat) : List Reg := [accR k 0, accR k 1, accR k 2]

theorem accR_mod (k n : Nat) : accR k n = [Reg.x5, .x6, .x7].getD ((k + n) % 3) .x5 := rfl

theorem acc_succ (k : Nat) : VG.Proof.Ed448.AArch64.acc (k + 1) = [accR k 1, accR k 2, accR k 0] := by
  simp only [VG.Proof.Ed448.AArch64.acc, VG.Proof.Ed448.AArch64.accR_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show k + 1 + 2 = k + 3 by omega, Nat.add_mod_right, Nat.add_zero]

theorem acc_cases (k : Nat) :
    VG.Proof.Ed448.AArch64.acc k = [.x5, .x6, .x7] ∨ VG.Proof.Ed448.AArch64.acc k = [.x6, .x7, .x5] ∨ VG.Proof.Ed448.AArch64.acc k = [.x7, .x5, .x6] := by
  simp only [VG.Proof.Ed448.AArch64.acc, VG.Proof.Ed448.AArch64.accR_mod]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod k, h] <;> simp

theorem acc_nodup (k : Nat) :
    [accR k 0, accR k 1, accR k 2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup := by
  have := VG.Proof.Ed448.AArch64.acc_cases k
  simp only [VG.Proof.Ed448.AArch64.acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem acc_colX (k : Nat) : ∀ r ∈ [Reg.x12, .x13, .x14, .x15, accR k 0, accR k 1, accR k 2],
    r ∈ VG.Proof.Ed448.AArch64.colX := by
  have := VG.Proof.Ed448.AArch64.acc_cases k
  simp only [VG.Proof.Ed448.AArch64.acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem accR_colX (k n : Nat) (hn : n < 3) : accR k n ∈ VG.Proof.Ed448.AArch64.colX := by
  have := VG.Proof.Ed448.AArch64.acc_colX k
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact this _ (by simp)

/-- A column: its terms, its low word stored at `ACC + 8k`, and the rest of
the accumulator passed on. -/
theorem column_ok {s : State} {base : Addr} (hs : VG.Proof.Ed448.AArch64.Wk s base) (k : Nat) (hk : k < 16)
    (hc : ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9)
    (hb : VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.acc k) + VG.Proof.Ed448.AArch64.colSum (VG.Proof.Ed448.AArch64.xw s.mem base) (VG.Proof.Ed448.AArch64.yw s.mem base) (mulCol k) < 2 ^ 192) :
    WP isa (.block (column k)) s fun s' =>
      (word s'.mem base (ACC + 8 * k)).toNat + 2 ^ 64 * VG.Proof.Ed448.AArch64.rv s' (VG.Proof.Ed448.AArch64.acc (k + 1)) =
        VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.acc k) + VG.Proof.Ed448.AArch64.colSum (VG.Proof.Ed448.AArch64.xw s.mem base) (VG.Proof.Ed448.AArch64.yw s.mem base) (mulCol k) ∧
      (∀ r, r ∉ VG.Proof.Ed448.AArch64.colX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside base (ACC + 8 * k) 8 s.mem s'.mem := by
  have hsub := VG.Proof.Ed448.AArch64.acc_colX k
  rw [column, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.terms_ok (VG.Proof.Ed448.AArch64.acc_nodup k) (mulCol k) s hs hc hb) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 : VG.Proof.Ed448.AArch64.Wk s1 base := hs.of_keeps k1 (fun h => by have := hsub _ h; simp [VG.Proof.Ed448.AArch64.colX] at this)
    (fun h => by have := hsub _ h; simp [VG.Proof.Ed448.AArch64.colX] at this)
  have hw : InRegions s1.wr (s1.gpr .x2 + BitVec.ofNat 64 (ACC + 8 * k)) 8 := by
    rw [hs1.x2]; exact ⟨_, hs1.wr, contains_sc (by simp only [ACC]; omega)⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_x ⟨by simp only [ACC]; omega, by simp only [ACC]; omega⟩ hw, ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  have hn := VG.Proof.Ed448.AArch64.acc_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, -⟩, ⟨h12, -⟩, -⟩ := hn
  refine ⟨?_, fun r hr => ?_, k1.rd, k1.wr, k1.sp, ?_⟩
  · rw [VG.Proof.Ed448.AArch64.acc_succ]
    simp only [VG.Proof.Ed448.AArch64.rv, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h01),
      RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h02), RegUpd.mem_write, hs1.x2, word_writeW_self]
    simp only [VG.Proof.Ed448.AArch64.acc, VG.Proof.Ed448.AArch64.rv] at e1 ⊢
    rw [show (BitVec.setWidth 64 (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0))).toNat = 0
      from rfl]
    omega
  · have hr0 : r ≠ accR k 0 := fun e => hr (e ▸ VG.Proof.Ed448.AArch64.accR_colX k 0 (by decide))
    rw [RegUpd.gpr_write_of_ne _ _ _ hr0]
    exact k1.gpr r (fun h => hr (hsub _ h))
  · simp only [RegUpd.mem_write, hs1.x2]
    rw [← k1.mem]; exact writeW_outside _ _ _ (by simp only [ACC]; omega)

theorem mv_succ_last (m : Mem) (base : Addr) :
    ∀ (o n : Nat), VG.Proof.Ed448.AArch64.mv m base o (n + 1) = VG.Proof.Ed448.AArch64.mv m base o n + 2 ^ (64 * n) * (word m base (o + 8 * n)).toNat
  | o, 0 => by simp [VG.Proof.Ed448.AArch64.mv]
  | o, n + 1 => by
    rw [VG.Proof.Ed448.AArch64.mv, VG.Proof.Ed448.AArch64.mv_succ_last m base (o + 8) n, VG.Proof.Ed448.AArch64.mv, VG.Proof.Ed448.AArch64.pow64_succ,
      show o + 8 + 8 * n = o + 8 * (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

/-- The columns' values: `Σ_{m<n} 2^(64m) colSum (mulCol (k + m))`, in Horner
form, whose only power is `2⁶⁴`. -/
def colsVal (xv yv : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => VG.Proof.Ed448.AArch64.colSum xv yv (mulCol k) + 2 ^ 64 * VG.Proof.Ed448.AArch64.colsVal xv yv (k + 1) n

theorem colsVal_succ_last (xv yv : Nat → Nat) :
    ∀ k n, VG.Proof.Ed448.AArch64.colsVal xv yv k (n + 1) = VG.Proof.Ed448.AArch64.colsVal xv yv k n + 2 ^ (64 * n) * VG.Proof.Ed448.AArch64.colSum xv yv (mulCol (k + n))
  | k, 0 => by simp [VG.Proof.Ed448.AArch64.colsVal]
  | k, n + 1 => by
    rw [VG.Proof.Ed448.AArch64.colsVal, VG.Proof.Ed448.AArch64.colsVal_succ_last xv yv (k + 1) n, VG.Proof.Ed448.AArch64.colsVal, VG.Proof.Ed448.AArch64.pow64_succ,
      show k + 1 + n = k + (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

theorem colSum_le (xv yv : Nat → Nat) :
    ∀ ts : List (Nat × Nat), (∀ t ∈ ts, xv t.1 < 2 ^ 64 ∧ yv t.2 < 2 ^ 64) →
      VG.Proof.Ed448.AArch64.colSum xv yv ts ≤ ts.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1))
  | [], _ => by simp [VG.Proof.Ed448.AArch64.colSum]
  | t :: ts, h => by
    rw [VG.Proof.Ed448.AArch64.colSum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h t List.mem_cons_self
    have hp : xv t.1 * yv t.2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := VG.Proof.Ed448.AArch64.colSum_le xv yv ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega

theorem colSum_congr (xv yv xv' yv' : Nat → Nat) (ts : List (Nat × Nat))
    (h : ∀ t ∈ ts, xv t.1 = xv' t.1 ∧ yv t.2 = yv' t.2) :
    VG.Proof.Ed448.AArch64.colSum xv yv ts = VG.Proof.Ed448.AArch64.colSum xv' yv' ts := by
  simp only [VG.Proof.Ed448.AArch64.colSum]
  exact congrArg List.sum (List.map_congr_left fun t ht => by rw [(h t ht).1, (h t ht).2])

theorem mulCol_hc : ∀ k < 16, ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9 := by decide
theorem mulCol_len : ∀ k < 16, (mulCol k).length ≤ 9 := by decide

theorem colX_x2 : Reg.x2 ∉ VG.Proof.Ed448.AArch64.colX := by decide
theorem colX_x26 : Reg.x26 ∉ VG.Proof.Ed448.AArch64.colX := by decide

/-- The first `n` columns of the product. -/
theorem columns_ok {s₀ : State} {base : Addr} (hs : VG.Proof.Ed448.AArch64.Wk s₀ base) (h0 : VG.Proof.Ed448.AArch64.rv s₀ (VG.Proof.Ed448.AArch64.acc 0) = 0) :
    ∀ n ≤ 16, WP isa (.block ((List.range n).flatMap column)) s₀ fun s =>
      (∀ r, r ∉ VG.Proof.Ed448.AArch64.colX → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Outside base ACC (8 * n) s₀.mem s.mem ∧
      VG.Proof.Ed448.AArch64.mv s.mem base ACC n + 2 ^ (64 * n) * VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.acc n) =
        VG.Proof.Ed448.AArch64.colsVal (VG.Proof.Ed448.AArch64.xw s₀.mem base) (VG.Proof.Ed448.AArch64.yw s₀.mem base) 0 n ∧
      VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.acc n) < 2 ^ 128
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _,
      by simp [VG.Proof.Ed448.AArch64.mv, VG.Proof.Ed448.AArch64.colsVal, h0], by rw [h0]; decide⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.columns_ok hs h0 n (by omega)) fun s ⟨g, rd, wr, sp, o, e, b⟩ => ?_
    have hsS : VG.Proof.Ed448.AArch64.Wk s base := ⟨(g _ VG.Proof.Ed448.AArch64.colX_x2).trans hs.x2, wr ▸ hs.wr, (g _ VG.Proof.Ed448.AArch64.colX_x26).trans hs.z⟩
    have hcn := VG.Proof.Ed448.AArch64.mulCol_hc n (by omega)
    have same : ∀ t ∈ mulCol n, VG.Proof.Ed448.AArch64.xw s.mem base t.1 = VG.Proof.Ed448.AArch64.xw s₀.mem base t.1 ∧
        VG.Proof.Ed448.AArch64.yw s.mem base t.2 = VG.Proof.Ed448.AArch64.yw s₀.mem base t.2 := fun t ht => by
      have := hcn t ht
      exact ⟨by rw [VG.Proof.Ed448.AArch64.xw, o.word (by simp only [XK, ACC]; omega) (by simp only [XK]; omega)],
        by rw [VG.Proof.Ed448.AArch64.yw, o.word (by simp only [YS, ACC]; omega) (by simp only [YS]; omega)]⟩
    have cs := VG.Proof.Ed448.AArch64.colSum_congr _ _ _ _ (mulCol n) same
    have cb := VG.Proof.Ed448.AArch64.colSum_le (VG.Proof.Ed448.AArch64.xw s.mem base) (VG.Proof.Ed448.AArch64.yw s.mem base) (mulCol n)
      fun t _ => ⟨(word s.mem base _).isLt, (word s.mem base _).isLt⟩
    have hwn := Nat.mul_le_mul_right ((2 ^ 64 - 1) * (2 ^ 64 - 1)) (VG.Proof.Ed448.AArch64.mulCol_len n (by omega))
    rw [List.flatMap_singleton]
    refine WP.mono (VG.Proof.Ed448.AArch64.column_ok hsS n (by omega) hcn (by omega))
      fun s' ⟨e', g', rd', wr', sp', o'⟩ => ?_
    refine ⟨fun r hr => (g' r hr).trans (g r hr), rd'.trans rd, wr'.trans wr, sp'.trans sp,
      (o.mono (Nat.le_refl _) (by omega)).trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [VG.Proof.Ed448.AArch64.mv_succ_last, Outside.mv_eq o' n ACC (by omega) (by simp only [ACC]; omega),
        VG.Proof.Ed448.AArch64.colsVal_succ_last, Nat.zero_add, VG.Proof.Ed448.AArch64.pow64_succ, ← cs]
      generalize 2 ^ (64 * n) = Q at e ⊢
      calc VG.Proof.Ed448.AArch64.mv s.mem base ACC n + Q * (word s'.mem base (ACC + 8 * n)).toNat +
            2 ^ 64 * Q * VG.Proof.Ed448.AArch64.rv s' (VG.Proof.Ed448.AArch64.acc (n + 1))
          = VG.Proof.Ed448.AArch64.mv s.mem base ACC n + Q * ((word s'.mem base (ACC + 8 * n)).toNat +
              2 ^ 64 * VG.Proof.Ed448.AArch64.rv s' (VG.Proof.Ed448.AArch64.acc (n + 1))) := by grind
        _ = VG.Proof.Ed448.AArch64.mv s.mem base ACC n + Q * VG.Proof.Ed448.AArch64.rv s (VG.Proof.Ed448.AArch64.acc n) + Q * VG.Proof.Ed448.AArch64.colSum (VG.Proof.Ed448.AArch64.xw s.mem base)
              (VG.Proof.Ed448.AArch64.yw s.mem base) (mulCol n) := by rw [e']; grind
        _ = _ := by rw [e]
    · omega

/-- Eight words' value, in Horner form. -/
def val8 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * (f 6 + 2 ^ 64 * f 7))))))

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- `val8` unfolded (stated, as `simp` would otherwise generate it at length). -/
theorem val8_eq (f : Nat → Nat) : VG.Proof.Ed448.AArch64.val8 f =
    f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
      2 ^ 64 * (f 6 + 2 ^ 64 * f 7)))))) := rfl

/-- The columns of `r + k s`: with `k` the left operands `0–7`, `r` the
left operands `8–15`, `s` the right operands `0–7` and one the right
operand 8. -/
theorem mulCols_sum (xv yv : Nat → Nat) (h1 : yv 8 = 1) :
    VG.Proof.Ed448.AArch64.colsVal xv yv 0 16 = VG.Proof.Ed448.AArch64.val8 xv * VG.Proof.Ed448.AArch64.val8 yv + VG.Proof.Ed448.AArch64.val8 (fun i => xv (8 + i)) := by
  simp only [VG.Proof.Ed448.AArch64.colsVal, VG.Proof.Ed448.AArch64.colSum, mulCol, VG.Proof.Ed448.AArch64.range8, List.filter_cons, List.filter_nil, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, and_self, and_true, and_false,
    decide_true, decide_false, ite_true, ite_false, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, VG.Proof.Ed448.AArch64.val8_eq, h1, Nat.mul_one,
    Nat.add_zero, Nat.zero_le, Nat.le_refl, Bool.false_eq_true]
  generalize 2 ^ 64 = B
  grind

theorem mv8_val (m : Mem) (base : Addr) (o : Nat) :
    VG.Proof.Ed448.AArch64.mv m base o 8 = VG.Proof.Ed448.AArch64.val8 fun i => (word m base (o + 8 * i)).toNat := by
  simp only [VG.Proof.Ed448.AArch64.mv8, VG.Proof.Ed448.AArch64.val8_eq, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h

theorem sq_add_le (n : Nat) : 2 ^ n * 2 ^ n + 2 ^ n ≤ 2 ^ (2 * n + 1) := by
  have : 2 ^ n ≤ 2 ^ (n + n) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_succ, Nat.mul_two, Nat.two_mul, Nat.pow_add]
  rw [Nat.pow_add] at this
  omega

/-- `columns`: `r + k s` into the sixteen words at `ACC`, from `k`, `r`, `s`
(each below `2^456`) and one at `XK`, `XK + 64`, `YS` and `YS + 64`. -/
theorem product_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hone : word s.mem base (YS + 64) = 1)
    (hk : VG.Proof.Ed448.AArch64.mv s.mem base XK 8 < 2 ^ 456) (hr : VG.Proof.Ed448.AArch64.mv s.mem base (XK + 64) 8 < 2 ^ 456)
    (hs : VG.Proof.Ed448.AArch64.mv s.mem base YS 8 < 2 ^ 456) :
    WP isa (.block columns) s fun t =>
      VG.Proof.Ed448.AArch64.mv t.mem base ACC 16 = VG.Proof.Ed448.AArch64.mv s.mem base (XK + 64) 8 + VG.Proof.Ed448.AArch64.mv s.mem base XK 8 * VG.Proof.Ed448.AArch64.mv s.mem base YS 8 ∧
      (∀ r, r ∉ .x26 :: VG.Proof.Ed448.AArch64.colX → t.gpr r = s.gpr r) ∧ t.gpr .x26 = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Outside base ACC 128 s.mem t.mem := by
  rw [columns, WP.block_append_iff]
  apply WP.mono (Q := fun (a : State) => VG.Proof.Ed448.AArch64.Wk a base ∧ VG.Proof.Ed448.AArch64.rv a (VG.Proof.Ed448.AArch64.acc 0) = 0 ∧ a.mem = s.mem ∧
    (∀ r, r ∉ [Reg.x26, .x5, .x6, .x7] → a.gpr r = s.gpr r) ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.sp = s.sp)
  · apply WP.of_runBlock
    simp only [Z, runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, hw, rfl⟩, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  intro a ⟨ha, h0, ma, ga, rda, wra, spa⟩
  refine WP.mono (VG.Proof.Ed448.AArch64.columns_ok ha h0 16 (Nat.le_refl _)) fun t ⟨gt, rdt, wrt, spt, ot, et, bt⟩ => ?_
  have hsum := VG.Proof.Ed448.AArch64.mulCols_sum (VG.Proof.Ed448.AArch64.xw a.mem base) (VG.Proof.Ed448.AArch64.yw a.mem base) (by rw [VG.Proof.Ed448.AArch64.yw, ma, Nat.mul_comm, hone]; rfl)
  have ex : VG.Proof.Ed448.AArch64.val8 (VG.Proof.Ed448.AArch64.xw a.mem base) = VG.Proof.Ed448.AArch64.mv s.mem base XK 8 := by rw [VG.Proof.Ed448.AArch64.mv8_val, ma]
  have ey : VG.Proof.Ed448.AArch64.val8 (VG.Proof.Ed448.AArch64.yw a.mem base) = VG.Proof.Ed448.AArch64.mv s.mem base YS 8 := by rw [VG.Proof.Ed448.AArch64.mv8_val, ma]
  have er : VG.Proof.Ed448.AArch64.val8 (fun i => VG.Proof.Ed448.AArch64.xw a.mem base (8 + i)) = VG.Proof.Ed448.AArch64.mv s.mem base (XK + 64) 8 := by
    rw [VG.Proof.Ed448.AArch64.mv8_val, ma]
    exact congrArg VG.Proof.Ed448.AArch64.val8 (funext fun i => by rw [VG.Proof.Ed448.AArch64.xw, show XK + 8 * (8 + i) = XK + 64 + 8 * i by omega])
  rw [hsum, ex, ey, er] at et
  refine ⟨?_, fun r hr => ?_, (gt _ VG.Proof.Ed448.AArch64.colX_x26).trans ha.z, rdt.trans rda, wrt.trans wra,
    spt.trans spa, by rw [← ma]; exact ot⟩
  · generalize hP : (2 : Nat) ^ (64 * 16) = P at et
    have hb : (2 : Nat) ^ 456 * 2 ^ 456 + 2 ^ 456 ≤ P :=
      Nat.le_trans (Nat.le_trans (VG.Proof.Ed448.AArch64.sq_add_le 456) (VG.Proof.Ed448.AArch64.pow_mono (a := 2 * 456 + 1) (b := 64 * 16) (by decide))) (Nat.le_of_eq hP)
    generalize (2 : Nat) ^ 456 = Q at hk hs hr hb
    have hp := Nat.mul_lt_mul'' hk hs
    have hA : VG.Proof.Ed448.AArch64.rv t (VG.Proof.Ed448.AArch64.acc 16) = 0 := by
      rcases Nat.eq_zero_or_pos (VG.Proof.Ed448.AArch64.rv t (VG.Proof.Ed448.AArch64.acc 16)) with h | h
      · exact h
      · have := Nat.mul_le_mul_left P h
        generalize P * VG.Proof.Ed448.AArch64.rv t (VG.Proof.Ed448.AArch64.acc 16) = A at et this
        generalize VG.Proof.Ed448.AArch64.mv s.mem base XK 8 * VG.Proof.Ed448.AArch64.mv s.mem base YS 8 = M at hp et
        omega
    rw [hA, Nat.mul_zero, Nat.add_zero] at et
    rw [et, Nat.add_comm]
  · simp only [List.mem_cons, not_or] at hr
    have h5 : r ≠ .x5 := by rintro rfl; exact hr.2 (by decide)
    have h6 : r ≠ .x6 := by rintro rfl; exact hr.2 (by decide)
    have h7 : r ≠ .x7 := by rintro rfl; exact hr.2 (by decide)
    have hr' : r ∉ [Reg.x26, .x5, .x6, .x7] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr.1, h5, h6, h7⟩
    rw [gt r hr.2, ga r hr']

/-- `8n` bytes at `base + o` are `n` words. -/
theorem decode_mv (m : Mem) (base : Addr) :
    ∀ (n o : Nat), Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (off base o) (8 * n)) = VG.Proof.Ed448.AArch64.mv m base o n
  | 0, _ => rfl
  | n + 1, o => by
    have e := VG.Proof.Ed448.words_step m (off base o) (8 * (n + 1)) 0 (by omega)
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Nat.mul_one, BitVec.add_zero] at e
    rw [e, show 8 * (n + 1) - 8 = 8 * n by omega, show off base o + BitVec.ofNat 64 8 = off base (o + 8)
      from Offset.add_add base o 8, VG.Proof.Ed448.AArch64.decode_mv m base n (o + 8), VG.Proof.Ed448.AArch64.mv]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit`. -/
section

/-!
# Ed448 scalar arithmetic on AArch64: the code as literals

The kernel checks each literal once; the taint and instruction checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.AArch64.scalarReduce
materialize_code Impl.Ed448.AArch64.scalarMulAdd

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarMain`. -/
section

/-!
# Ed448 scalar reduction on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarReduceContract` it uses, stated for AArch64), and the
correctness of `vg_ed448_scalar_reduce` against it: the working space is
written only where the callee-saved registers are saved, so the input is
read unchanged; they are restored before the result is written.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- A buffer of `n` bytes is its own encoding. -/
theorem bytesAt_encode (m : Mem) (q : Addr) (n : Nat) :
    VG.Spec.Ed448.bytesAt m q n = Spec.Ed448.encodeLE n (VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt m q n)) := by
  rw [VG.Proof.Ed448.encodeLE_eq, VG.Proof.Ed448.decodeLE_eq, bytesAt_eq, Proof.X25519.leNum_bytesAt_read,
    ← Proof.X25519.bytesAt_leBytes]

/-- `vg_ed448_scalar_reduce(out = x0, wide = x1, scratch = x2)`. -/
def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 114⟩] ∧ s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  post s t := VG.Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- `finish`: the callee-saved registers restored, and the remainder written to the 57 bytes at `q`. -/
theorem finish_ok {s : State} {base q : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : VG.Proof.Ed448.AArch64.Saved base g s.mem)
    (hq : s.gpr .x0 = q) (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block finish) s fun t =>
      VG.Spec.Ed448.bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (VG.Proof.Ed448.AArch64.rem s) ∧ (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧
      (∀ r, r ∉ Reg.x12 :: VG.Proof.Ed448.AArch64.savedRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  rw [finish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.restoreRegs_ok hb hw hsv) fun a ⟨ra, ka⟩ => ?_
  have qa : a.gpr .x0 = q := (ka.gpr _ (by decide)).trans hq
  refine WP.mono (VG.Proof.Ed448.AArch64.outStore_ok qa (ka.wr ▸ hwo)) fun t ⟨vt, _, gt, _, _, spt⟩ => ?_
  refine ⟨?_, fun p hp => (gt _ ((by decide : ∀ p ∈ saved, p.1 ≠ .x12) p hp)).trans (ra p hp),
    fun r hr => ?_, spt.trans ka.sp⟩
  · rw [VG.Proof.Ed448.AArch64.bytesAt_encode, vt, show VG.Proof.Ed448.AArch64.rem a = VG.Proof.Ed448.AArch64.rem s from Keeps.rv_eq ka (by decide)]
  · simp only [List.mem_cons, not_or] at hr
    rw [gt r hr.1, ka.gpr r hr.2]

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa VG.Impl.Ed448.AArch64.scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [VG.Impl.Ed448.AArch64.scalarReduce]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.saveRegs_ok .x2 rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.consts_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have rdw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  have inw : ∀ d n, d + n ≤ 114 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x1 + BitVec.ofNat 64 d) n :=
    fun d n h => ⟨⟨s.gpr .x1, 114⟩, by rw [rdw₂, hr]; simp,
      by rw [x1₂]; exact Offset.contains_base _ h (by omega)⟩
  refine WP.mono (VG.Proof.Ed448.AArch64.init114_ok s₂ (inw 112 1 (by omega)) (inw 113 1 (by omega)))
    fun s₃ ⟨v₃, b₃, k₃⟩ => ?_
  have c₃ : VG.Proof.Ed448.AArch64.Consts s₃ := c₂.of_keeps k₃ (by decide)
  have x1₃ : s₃.gpr .x1 = s.gpr .x1 := (k₃.gpr _ (by decide)).trans x1₂
  have m₃ : s₃.mem = s₁.mem := k₃.mem.trans k₂.mem
  apply WP.seq
  have hi : VG.Proof.Ed448.AArch64.LoopInv 114 s₃ 14 s₃ := by
    refine ⟨by decide, by decide, b₃, ?_, Keeps.refl _ _⟩
    rw [v₃, k₃.mem, k₃.gpr .x1 (by decide)]
    simp only [Nat.reduceMul, Nat.reduceSub]
    have hlt := decodeLE_lt' (VG.Spec.Ed448.bytesAt s₂.mem (s₂.gpr .x1 + BitVec.ofNat 64 112) 2)
    rw [VG.Proof.Ed448.bytesAt_length] at hlt
    have : (256 : Nat) ^ 2 < VG.Spec.Ed448.L := by decide +kernel
    exact (Nat.mod_eq_of_lt (by omega)).symm
  refine WP.mono (VG.Proof.Ed448.AArch64.scalarLoop_ok s₃ c₃ (by decide) hi fun k hk => by
      rw [k₃.rd, k₃.wr, ← x1₂.trans x1₃.symm]
      exact inw (8 * k) 8 (by omega)) fun s₄ ⟨v₄, k₄⟩ => ?_
  have x2₄ : s₄.gpr .x2 = s.gpr .x2 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have wr₄ : s₄.wr = s.wr := by rw [k₄.wr, k₃.wr, k₂.wr, wr₁]
  have sv₄ : VG.Proof.Ed448.AArch64.Saved (s.gpr .x2) s.gpr s₄.mem := by rw [k₄.mem, m₃]; exact sv₁
  refine WP.mono (VG.Proof.Ed448.AArch64.finish_ok x2₄ (wr₄ ▸ hws) sv₄ x0₄ (wr₄ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₄.sp.trans (k₃.sp.trans (k₂.sp.trans sp₁)))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals
      rw [gt _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  · show VG.Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114)
    rw [bt, v₄, x1₃, m₃, VG.Proof.Ed448.AArch64.bytesAt_outside o₁ (by decide) hd (by decide)]
    rfl

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarMulAddMain`. -/
section

/-!
# Ed448 scalar multiply-add on AArch64: the whole function

`vg_ed448_scalar_mul_add` copies `k`, `r` and `s` to the working space,
forms `r + k s` in sixteen words by product scanning, and reduces them with
the loop of `vg_ed448_scalar_reduce`, from a zero remainder. The working
space is written only where the callee-saved registers are saved, the
operands and the product, so the inputs are read unchanged and the saved
registers are restored.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_mul_add(out = x0, r = x1, k = x2, s = x3, scratch = x4)`. -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.gpr .x2, 57⟩, ⟨s.gpr .x3, 57⟩] ∧
    s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 57⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  post s t := VG.Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)
    (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x3) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

/-- The loop over the words at `ACC`, with a zero remainder. -/
theorem accInit_ok (s : State) :
    WP isa (.block accInit) s fun t =>
      t.gpr .x1 = s.gpr .x2 + BitVec.ofNat 64 ACC ∧ VG.Proof.Ed448.AArch64.rem t = 0 ∧ t.gpr .x3 = BitVec.ofNat 64 128 ∧
      Keeps [.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [accInit, zeroHigh, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show ACC < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      Ed25519.AArch64.read_x]
  · simp only [VG.Proof.Ed448.AArch64.rem, VG.Proof.Ed448.AArch64.rv, R, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem pow256_57 : (256 : Nat) ^ 57 = 2 ^ 456 :=
  calc (256 : Nat) ^ 57 = (2 ^ 8) ^ 57 := rfl
    _ = 2 ^ (8 * 57) := (Nat.pow_mul 2 8 57).symm
    _ = 2 ^ 456 := by rw [show 8 * 57 = 456 from rfl]

/-- The registers `vg_ed448_scalar_mul_add` changes before it restores the
callee-saved ones. -/
def mulAddClob : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26]

theorem clob_sub : ∀ r ∈ VG.Proof.Ed448.AArch64.clob, r ∈ VG.Proof.Ed448.AArch64.mulAddClob := by decide
theorem accInit_sub : ∀ r ∈ [Reg.x1, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11], r ∈ VG.Proof.Ed448.AArch64.mulAddClob := by
  decide
theorem consts_sub : ∀ r ∈ VG.Proof.Ed448.AArch64.constRegs, r ∈ VG.Proof.Ed448.AArch64.mulAddClob := by decide
theorem colX_sub : ∀ r ∈ Reg.x26 :: VG.Proof.Ed448.AArch64.colX, r ∈ VG.Proof.Ed448.AArch64.mulAddClob := by decide
theorem operands_sub : ∀ r ∈ [Reg.x2, .x5], r ∈ VG.Proof.Ed448.AArch64.mulAddClob := by decide

theorem decodeLE_lt456 (m : Mem) (p : Addr) : VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt m p 57) < 2 ^ 456 := by
  have h := decodeLE_lt' (VG.Spec.Ed448.bytesAt m p 57)
  rw [VG.Proof.Ed448.bytesAt_length, VG.Proof.Ed448.AArch64.pow256_57] at h
  exact h

theorem scalarMulAdd_correct {s : State} (hs : scalarMulAddLocal.pre s) :
    WP isa VG.Impl.Ed448.AArch64.scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, dr, dk, ds⟩ := hs
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x4 = b := ⟨_, rfl⟩
  rw [hbase] at hw dr dk ds
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hin : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s.gpr r, 57⟩ : Region) ∈ s.rd ++ s.wr := by
    intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl <;> rw [hr] <;> simp
  rw [VG.Impl.Ed448.AArch64.scalarMulAdd]
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.saveRegs_ok .x4 hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  have in₁ : ∀ r ∈ [Reg.x1, .x2, .x3], (⟨s₁.gpr r, 57⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [g₁, rd₁, wr₁]; exact hin
  refine WP.mono (VG.Proof.Ed448.AArch64.operands_ok (s := s₁) (base := base) (by rw [g₁]; exact hbase) (wr₁ ▸ hws)
    (in₁ _ (by decide)) (in₁ _ (by decide)) (in₁ _ (by decide)) (by rw [g₁]; exact dr)
    (by rw [g₁]; exact dk) (by rw [g₁]; exact ds))
    fun s₂ ⟨vk₂, vr₂, vs₂, one₂, o₂, x2₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  have ek : VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₁.mem (s₁.gpr .x2) 57) = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) := by
    rw [g₁, VG.Proof.Ed448.AArch64.bytesAt_outside o₁ (by decide) dk (by decide)]
  have er : VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₁.mem (s₁.gpr .x1) 57) = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) := by
    rw [g₁, VG.Proof.Ed448.AArch64.bytesAt_outside o₁ (by decide) dr (by decide)]
  have es : VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s₁.mem (s₁.gpr .x3) 57) = VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x3) 57) := by
    rw [g₁, VG.Proof.Ed448.AArch64.bytesAt_outside o₁ (by decide) ds (by decide)]
  rw [ek] at vk₂; rw [er] at vr₂; rw [es] at vs₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.product_ok x2₂ (wr₂ ▸ wr₁ ▸ hws) one₂ (vk₂ ▸ VG.Proof.Ed448.AArch64.decodeLE_lt456 _ _)
    (vr₂ ▸ VG.Proof.Ed448.AArch64.decodeLE_lt456 _ _) (vs₂ ▸ VG.Proof.Ed448.AArch64.decodeLE_lt456 _ _))
    fun s₃ ⟨v₃, g₃, z₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [vk₂, vr₂, vs₂] at v₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.consts_ok s₃) fun s₄ ⟨c₄, k₄⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.accInit_ok s₄) fun s₅ ⟨x1₅, r₅, x3₅, k₅⟩ => ?_
  have c₅ : VG.Proof.Ed448.AArch64.Consts s₅ := c₄.of_keeps k₅ (by decide)
  have x2₄ : s₄.gpr .x2 = base := (k₄.gpr _ (by decide)).trans ((g₃ _ (by decide)).trans x2₂)
  have m₅ : s₅.mem = s₃.mem := k₅.mem.trans k₄.mem
  have rdw₅ : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [k₅.rd, k₅.wr, k₄.rd, k₄.wr, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]
  apply WP.seq
  have hi : VG.Proof.Ed448.AArch64.LoopInv 128 s₅ 16 s₅ := by
    refine ⟨by decide, by decide, x3₅, ?_, Keeps.refl _ _⟩
    rw [r₅]; rfl
  refine WP.mono (VG.Proof.Ed448.AArch64.scalarLoop_ok s₅ c₅ (by decide) hi fun k hk => by
      rw [rdw₅, x1₅, x2₄, Offset.add_add]
      exact ⟨_, List.mem_append_right _ hws, contains_sc (by simp only [ACC]; omega)⟩)
    fun s₆ ⟨v₆, k₆⟩ => ?_
  have x2₆ : s₆.gpr .x2 = base := by rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), x2₄]
  have g₆ : ∀ r, r ∉ VG.Proof.Ed448.AArch64.mulAddClob → s₆.gpr r = s.gpr r := fun r hr' => by
    rw [k₆.gpr r fun h => hr' (VG.Proof.Ed448.AArch64.clob_sub r h), k₅.gpr r fun h => hr' (VG.Proof.Ed448.AArch64.accInit_sub r h),
      k₄.gpr r fun h => hr' (VG.Proof.Ed448.AArch64.consts_sub r h), g₃ r fun h => hr' (VG.Proof.Ed448.AArch64.colX_sub r h),
      g₂ r fun h => hr' (VG.Proof.Ed448.AArch64.operands_sub r h), g₁]
  have x0₆ : s₆.gpr .x0 = s.gpr .x0 := g₆ _ (by decide)
  have wr₆ : s₆.wr = s.wr := by rw [k₆.wr, k₅.wr, k₄.wr, wr₃, wr₂, wr₁]
  have sv₆ : VG.Proof.Ed448.AArch64.Saved base s.gpr s₆.mem := by
    intro p hp
    have hl := (VG.Proof.Ed448.AArch64.saved_ok p hp).2
    rw [k₆.mem, m₅, Ed25519.AArch64.Outside.word o₃ (by simp only [ACC]; omega) (by omega),
      Ed25519.AArch64.Outside.word o₂ (by simp only [XK]; omega) (by omega)]
    exact sv₁ p hp
  refine WP.mono (VG.Proof.Ed448.AArch64.finish_ok x2₆ (wr₆ ▸ hws) sv₆ x0₆ (wr₆ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans
    (sp₃.trans (sp₂.trans sp₁)))))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals rw [gt _ (by decide), g₆ _ (by decide)]
  · show VG.Spec.Ed448.bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarMulAdd (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)
      (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) (VG.Spec.Ed448.bytesAt s.mem (s.gpr .x3) 57)
    rw [bt, v₆, x1₅, x2₄, m₅, show (128 : Nat) = 8 * 16 from rfl, VG.Proof.Ed448.AArch64.decode_mv, v₃]
    rfl

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified`. -/
section

/-!
# Ed448 scalar arithmetic on AArch64: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses: only the arguments, which
are public, do. A concrete witness proves the signature contract is
satisfiable.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

def scalarReduceSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa VG.Impl.Ed448.AArch64.scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  VG.Proof.Ed448.AArch64.scalarReduce_correct hs

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub VG.Impl.Ed448.AArch64.scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h0, h1, h2]

theorem scalarReduce_verified : Verified AArch64.target VG.Impl.Ed448.AArch64.scalarReduce
    (Spec.Ed448.scalarReduceContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Ed448.AArch64.scalarReduce_ok VG.Proof.Ed448.AArch64.scalarReduce_ct (by
    sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, VG.Proof.Ed448.AArch64.scalarReduceLocal]
      [scalarReduceSat] using VG.Proof.Ed448.AArch64.scalarReduceSat)

def scalarMulAddSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x5000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa VG.Impl.Ed448.AArch64.scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  VG.Proof.Ed448.AArch64.scalarMulAdd_correct hs

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub VG.Impl.Ed448.AArch64.scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

theorem scalarMulAdd_verified : Verified AArch64.target VG.Impl.Ed448.AArch64.scalarMulAdd
    (Spec.Ed448.scalarMulAddContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Ed448.AArch64.scalarMulAdd_ok VG.Proof.Ed448.AArch64.scalarMulAdd_ct (by
    sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, VG.Proof.Ed448.AArch64.scalarMulAddLocal]
      [scalarMulAddSat] using VG.Proof.Ed448.AArch64.scalarMulAddSat)

end VG.Proof.Ed448.AArch64

end
