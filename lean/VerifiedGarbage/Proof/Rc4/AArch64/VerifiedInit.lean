module

public import VerifiedGarbage.Impl.Rc4.AArch64.Fn
public meta import VerifiedGarbage.Impl.Rc4.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Clears
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Lit
public import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Rc4.AArch64.Lit
meta import VerifiedGarbage.Impl.Rc4.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64
meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! ### `Rc4.AArch64.Taint`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Key scheduling has no secret-dependent control flow or memory address:
the key bytes, `j` and the table indices stay in vector registers. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2])) init := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- `init`, then what it leaves cleared: the vector registers that held the
table and the key (`v0`–`v7`, `v16`–`v31`), and the high halves of `v8`–`v13`,
whose low halves it restores and which the calling convention does not
preserve, from `x9`, zeroed first. -/
abbrev initCleared : Prog isa := Impl.Rc4.AArch64.Fn.init

/-- `initCleared` returns without secret residue, with a 32-bit result
(`RTaintL.noResidue_of_check`, which sees the low and high halves of
`v8`–`v13` public apart). -/
theorem initCleared_noResidue (k : Contract isa) : NoResidue initCleared k 32 :=
  RTaintL.noResidue_of_check ⟨_, by taint_decide⟩ k

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.KsaGroup`, which only this module used -/

section

/-! ### `Rc4.AArch64.KsaStep`, which only this module used -/

section

/-!
# The key schedule's lanes

`keyByte_ok`: the next key byte is added to `j`, and the key pointer `x7`
and the bytes left before the key repeats, `x5`, advance (wrapping).
`ksaSwap_ok`: then the swap step is the specification's scheduling round.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem mod_succ_wrap {n L : Nat} (h : n % L + 1 = L) : (n + 1) % L = 0 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = L * (n / L + 1) by rw [Nat.mul_add]; omega_using [h, this]]
  exact Nat.mul_mod_right _ _

theorem mod_succ_lt {n L : Nat} (h : n % L + 1 < L) : (n + 1) % L = n % L + 1 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = (n % L + 1) + L * (n / L) by omega_using [this], Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h]

theorem low8 (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega_using []

theorem keyLoad_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = bc J) :
    WP isa (.block [.ldrb .x6 .x7 0, .vop (.dup .b16 .v6 .x6), .vop (.add .b16 (dq 0) (dq 0) .v6),
      .addImm .x .x7 .x7 1, .subImm .x .x5 .x5 1]) s fun t =>
      t.v (dq 0) = bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 (n % L) + 1 ∧ t.gpr .x5 = BitVec.ofNat 64 (L - n % L - 1) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  have hb := region_offset _ _ _ (n % L) 1 (by omega_using [hL', hm]) (by omega_using [hm]) hkey
  have hj' : s.v .v0 = bc J := hj
  have h1 : BitVec.ofNat 64 (L - n % L) - 1#64 = BitVec.ofNat 64 (L - n % L - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hm])
  have d0 : dq 0 = .v0 := rfl
  rrun [d0, hb, read_byte', hj', h7, h5, low8, bc_lit, add_bc, h1]
  refine ⟨fun r a b c => ?_, fun v a b => ?_, ?_⟩
  · simp [a, b, c]
  · simp [a, b]
  · simp [State.write, State.setV]

theorem keyByte_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = bc J) :
    WP isa keyByte s fun t =>
      t.v (dq 0) = bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 ((n + 1) % L) ∧
      t.gpr .x5 = BitVec.ofNat 64 (L - (n + 1) % L) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  unfold keyByte
  refine WP.seq (WP.mono (keyLoad_ok hL hL' h7 h5 hkey hj)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  apply WP.ite _ (eval_zero' a .x5 a5 (by omega_using [hL']))
  · intro hz
    have hw : n % L + 1 = L := by simp at hz; omega_using [hm, hz]
    have a0 : a.gpr .x0 = K := by rw [ag _ (by decide) (by decide) (by decide), h0]
    have a1 : a.gpr .x1 = BitVec.ofNat 64 L := by rw [ag _ (by decide) (by decide) (by decide), h1]
    rrun [a0, a1]
    refine ⟨aj, ?_, ?_, fun r r5 r6 r7 => ?_, av, am, ard, awr, ?_⟩
    · rw [mod_succ_wrap hw]; simp
    · rw [mod_succ_wrap hw, Nat.sub_zero]
    · simp only [r5, r7, ite_false]; exact ag r r5 r6 r7
    · simp only [State.write]; exact asp
  · intro hnz
    have hlt : n % L + 1 < L := by simp at hnz; omega_using [hnz]
    refine WP.block_nil ⟨aj, ?_, ?_, ag, av, am, ard, awr, asp⟩
    · rw [a7, mod_succ_lt hlt, Offset.add_ofNat_add_one]
    · rw [a5, mod_succ_lt hlt, Nat.sub_add_eq]

theorem byte_rearr (a b c d : BitVec 8) : a + b - d + c = a + c + b - d := by bv_omega

/-- A scheduling round at lane `l` of the group whose base is `B`, once the
key byte is in `j`. -/
theorem ksaSwap_ok {l B n : Nat} (hl : l < 16) (hn : n = B + l) (hn' : n < 256) {key : List Byte}
    {s : State} (hk : Consts s) (ht : TableIn s B (schedulePrefix key n).1)
    (hj : s.v (dq 0) = bc ((schedulePrefix key n).2 + key.getD (n % key.length) 0 - bB B))
    (hsi : s.v si = bc (tbyte s.v l)) :
    ∃ s', runBlock isa (swapStep false l) s = some s' ∧
      TableIn s' B (schedulePrefix key (n + 1)).1 ∧
      s'.v (dq 0) = bc ((schedulePrefix key (n + 1)).2 - bB B) ∧
      s'.v si = bc (tbyte s'.v (l + 1)) ∧ Only stepRegs s s' := by
  have hS := schedule_succ key n
  simp only [scheduleRound] at hS
  generalize schedulePrefix key n = st at ht hj hS
  obtain ⟨s₁, run₁, t₁, j₁, i₁, -, o₁⟩ :=
    swapStep_run false hl hk hj hsi (NB := 0) fun h => absurd h (by decide)
  have hR : ∀ k < 256, tbyte s.v k = st.1.getD (BitVec.ofNat 8 (B + k)).toNat 0 := ht
  have ha : tbyte s.v l = st.1.getD n 0 := by
    rw [hR l (by omega_using [hl]), ← hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn']
  have hJ : st.2 + key.getD (n % key.length) 0 - bB B + tbyte s.v l =
      st.2 + st.1.getD n 0 + key.getD (n % key.length) 0 - bB B := by rw [ha, byte_rearr]
  rw [hJ] at t₁ j₁ i₁
  refine ⟨s₁, run₁, fun k hk => ?_, by rw [j₁, hS], ?_, o₁⟩
  · rw [hS, t₁ k hk, swapR_eq st.1 (by omega_using [hl]) hR _ hk, hn]
  · rw [i₁, t₁ _ (by omega_using [hl])]

end VG.Proof.Rc4.AArch64

end

end


/-!
# The key schedule's groups

`ksaLane_ok`: a lane of the key schedule is a scheduling round;
`ksaGroup_ok`: sixteen lanes and the rotation take the group with base `B`
to the next, with base `B + 16`; `ksaLoop_ok`: sixteen groups take the
identity table to the key schedule, its registers back where they started.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The key schedule's globals: the key at `K` of `L` bytes in the memory
`M`, and the state `s₀` that the setup leaves. -/
structure KGlob where
  K : Addr
  L : Nat
  M : Mem
  s₀ : State

def KGlob.key (g : KGlob) : List Byte := bytesAt g.M g.K g.L

structure KGlob.Ok (g : KGlob) : Prop where
  pos : 0 < g.L
  le : g.L ≤ 256
  x0 : g.s₀.gpr .x0 = g.K
  x1 : g.s₀.gpr .x1 = BitVec.ofNat 64 g.L
  key : InRegions (g.s₀.rd ++ g.s₀.wr) g.K g.L

/-- Lane `l` of the group whose base is `B`: `B + l` rounds done. -/
structure KsaInv (g : KGlob) (B l : Nat) (s : State) : Prop where
  consts : Consts s
  table : TableIn s B (schedulePrefix g.key (B + l)).1
  j : s.v (dq 0) = bc ((schedulePrefix g.key (B + l)).2 - bB B)
  si : s.v si = bc (tbyte s.v l)
  x7 : s.gpr .x7 = g.K + BitVec.ofNat 64 ((B + l) % g.L)
  x5 : s.gpr .x5 = BitVec.ofNat 64 (g.L - (B + l) % g.L)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  x4 : s.gpr .x4 = BitVec.ofNat 64 (16 - B / 16)
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  vkept : ∀ r, r ∉ stepRegs → s.v r = g.s₀.v r
  mem : s.mem = g.M
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

theorem sub_add_comm8 (x y z : BitVec 8) : x - y + z = x + z - y := by bv_omega

theorem ksaLane_ok {g : KGlob} (hg : g.Ok) {B l : Nat} (hl : l < 16) (hB : B + l < 256) {s : State}
    (h : KsaInv g B l s) :
    WP isa (.seq keyByte (.block (swapStep false l))) s (KsaInv g B (l + 1)) := by
  have h0 : s.gpr .x0 = g.K := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x0]
  have h1 : s.gpr .x1 = BitVec.ofNat 64 g.L := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x1]
  have hkey : InRegions (s.rd ++ s.wr) g.K g.L := by rw [h.rd, h.wr]; exact hg.key
  refine WP.seq (WP.mono (keyByte_ok hg.pos (by have := hg.le; omega_arith) h0 h1 h.x7 h.x5 hkey h.j)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  have hkb : s.mem (g.K + BitVec.ofNat 64 ((B + l) % g.L)) =
      g.key.getD ((B + l) % g.key.length) 0 := by
    rw [KGlob.key, bytes_length, bytes_get _ _ _ _ (Nat.mod_lt _ hg.pos), h.mem]
  have aj' : a.v (dq 0) = bc ((schedulePrefix g.key (B + l)).2 +
      g.key.getD ((B + l) % g.key.length) 0 - bB B) := by rw [aj, hkb, sub_add_comm8]
  have ka : Consts a := h.consts.congr fun r hr => av r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have tba : ∀ k < 256, tbyte a.v k = tbyte s.v k := fun k hk =>
    tbyte_congr (fun q hq => av _ ((show NotTable (dq 0) by decide) q hq)
      ((show NotTable .v6 by decide) q hq)) hk
  have ta : TableIn a B (schedulePrefix g.key (B + l)).1 := fun k hk => by
    rw [tba k hk]; exact h.table k hk
  have sia : a.v si = bc (tbyte a.v l) := by
    rw [av _ (by decide) (by decide), h.si, tba l (by omega_arith)]
  obtain ⟨t, run, tt, tj, tsi, to⟩ := ksaSwap_ok hl rfl hB ka ta aj' sia
  refine WP.of_runBlock ⟨t, run, ?_⟩
  have tg := to.gpr
  exact {
    consts := consts_of_only ka to
    table := tt
    j := tj
    si := tsi
    x7 := by rw [tg, a7]; rfl
    x5 := by rw [tg, a5]; rfl
    x8 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x8
    x4 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x4
    gpr := fun r r4 r5 r6 r7 r8 => by rw [tg, ag r r5 r6 r7]; exact h.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [to.2 r hr, av r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))]
      exact h.vkept r hr
    mem := by rw [to.mem, am]; exact h.mem
    rd := by rw [to.rd, ard]; exact h.rd
    wr := by rw [to.wr, awr]; exact h.wr
    sp := by rw [to.sp, asp]; exact h.sp }

theorem ksaLanes_ok {g : KGlob} (hg : g.Ok) {B : Nat} (hB : B + 16 ≤ 256) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : KsaInv g B 0 s) : WP isa (scheduleLanes n) s (KsaInv g B n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega_arith)) fun t ht => ksaLane_ok hg (by omega_arith) (by omega_arith) ht)

theorem subX4_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x4 1]) s fun t =>
      t.gpr .x4 = s.gpr .x4 - 1 ∧ (∀ r, r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rrun
  refine ⟨fun r hr => by simp [hr], by simp [State.write]⟩

theorem ksaGroup_ok {g : KGlob} (hg : g.Ok) {B : Nat} (hB16 : B % 16 = 0) (hB : B < 256) {s : State}
    (h : KsaInv g B 0 s) : WP isa scheduleGroup s (KsaInv g (B + 16) 0) := by
  apply WP.seq (WP.mono (ksaLanes_ok hg (by omega_arith) (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (rotate_ok false h₁.consts h₁.j (NB := 0) fun e => absurd e (by decide))
    fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  refine WP.mono (subX4_ok t) fun u ⟨u4, ug, uv, um, urd, uwr, usp⟩ => ?_
  have tbu : tbyte u.v = tbyte t.v := by rw [uv]
  exact {
    consts := h₁.consts.congr fun r hr => by
      rw [uv]; exact vv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    table := fun k hk => by
      rw [tbu, tab k hk, h₁.table _ (by omega_arith), ofNat_wrap]
    j := by rw [uv, j, byte_shift]
    si := by
      rw [uv, vv _ (by decide), h₁.si, tab 0 (by decide)]
    x7 := by
      rw [ug _ (by decide), gg _ (by decide), h₁.x7, show B + 16 + 0 = B + 16 from rfl]
    x5 := by rw [ug _ (by decide), gg _ (by decide), h₁.x5]
    x8 := by
      rw [ug _ (by decide), x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
        BitVec.ofNat_add_ofNat]
    x4 := by
      rw [u4, gg _ (by decide), h₁.x4, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith)]
      congr 1; omega_arith
    gpr := fun r r4 r5 r6 r7 r8 => by rw [ug r r4, gg r r8]; exact h₁.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [uv]
      by_cases hn : r = negBase
      · subst hn; simp only [Bool.false_eq_true, ite_false] at nb; rw [nb]; exact h₁.vkept _ hr
      · rw [vv r (by
          simp only [rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
            not_and]
          exact ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
            fun a ha e => hr (e ▸ treg_step a ha)⟩)]
        exact h₁.vkept r hr
    mem := by rw [um, m]; exact h₁.mem
    rd := by rw [urd, rd]; exact h₁.rd
    wr := by rw [uwr, wr]; exact h₁.wr
    sp := by rw [usp, sp]; exact h₁.sp }

/-- A group about to start, `m` groups before the end. -/
def KLoopInv (g : KGlob) (m : Nat) (s : State) : Prop :=
  ∃ B, m = 16 - B / 16 ∧ B % 16 = 0 ∧ B < 256 ∧ KsaInv g B 0 s

theorem ksaLoop_ok {g : KGlob} (hg : g.Ok) (m : Nat) {s : State} (h : KLoopInv g m s) :
    WP isa (.loop scheduleGroup (.nonzero .x .x4)) s (KsaInv g 256 0) := by
  refine WP.loop (M := isa) (KLoopInv g) ?_ m s h
  intro m s ⟨B, hm, hB16, hB, h⟩
  refine WP.mono (ksaGroup_ok hg hB16 hB h) fun t ht => ?_
  have flag := eval_nonzero' t .x4 ht.x4 (by omega_arith)
  by_cases hend : B + 16 = 256
  · left
    exact ⟨by rw [flag]; simp [hend], hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega_arith, 16 - (B + 16) / 16, by omega_arith, B + 16, rfl, by omega_arith,
      by omega_arith, ht⟩

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.Init`, which only this module used -/

section

/-! ### `Rc4.AArch64.KsaSetup`, which only this module used -/

section

/-!
# The key schedule's setup

`ksaSetup_ok`: the setup saves the callee-saved vector registers it uses,
leaves the constants, the identity table in `v16`–`v31` (lane numbers, and
their XORs with 64, 128 and 192), `j = 0`, `S[0] = 0`, the key pointer and
length, sixteen groups to go and the base `0`: the first group's `KsaInv`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ident_xor : ∀ q < 4, laneNums q ^^^ bc 64#8 = laneNums (q + 4) ∧
    laneNums q ^^^ bc 128#8 = laneNums (q + 8) ∧ laneNums (q + 4) ^^^ bc 128#8 = laneNums (q + 12) := by
  decide +kernel

/-- The identity table's code, written out. -/
def identCode : List Instr :=
  [.vop (.mov .v16 .v8), .vop (.mov .v17 .v9), .vop (.mov .v18 .v10), .vop (.mov .v19 .v11),
   eorV .v20 .v8 .v12, eorV .v21 .v9 .v12, eorV .v22 .v10 .v12, eorV .v23 .v11 .v12,
   eorV .v24 .v8 .v13, eorV .v25 .v9 .v13, eorV .v26 .v10 .v13, eorV .v27 .v11 .v13,
   eorV .v28 .v20 .v13, eorV .v29 .v21 .v13, eorV .v30 .v22 .v13, eorV .v31 .v23 .v13]

theorem identCode_eq :
    (List.range 4).map (fun r => .vop (.mov (treg r) (lanes r))) ++
    (List.range 4).map (fun r => eorV (treg (4 + r)) (lanes r) c64) ++
    (List.range 4).map (fun r => eorV (treg (8 + r)) (lanes r) c128) ++
    (List.range 4).map (fun r => eorV (treg (12 + r)) (treg (4 + r)) c128) = identCode := by
  decide

theorem ident_ok {s : State} (hk : Consts s) :
    WP isa (.block identCode) s fun t =>
      (∀ q < 16, t.v (treg q) = laneNums q) ∧ (∀ v, NotTable v → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain l0 : s.v .v8 = laneNums 0 := hk.lns 0 (by decide)
  obtain l1 : s.v .v9 = laneNums 1 := hk.lns 1 (by decide)
  obtain l2 : s.v .v10 = laneNums 2 := hk.lns 2 (by decide)
  obtain l3 : s.v .v11 = laneNums 3 := hk.lns 3 (by decide)
  have k64 : s.v .v12 = bc 64 := hk.c64
  have k128 : s.v .v13 = bc 128 := hk.c128
  obtain x0 := ident_xor 0 (by decide)
  obtain x1 := ident_xor 1 (by decide)
  obtain x2 := ident_xor 2 (by decide)
  obtain x3 := ident_xor 3 (by decide)
  simp only [Nat.reduceAdd] at x0 x1 x2 x3
  unfold identCode eorV
  rrun [l0, l1, l2, l3, k64, k128, x0.1, x0.2.1, x0.2.2, x1.1, x1.2.1, x1.2.2, x2.1, x2.2.1,
    x2.2.2, x3.1, x3.2.1, x3.2.2]
  refine ⟨fun q hq => ?_, fun v hv => ?_, ?_⟩
  · rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
      q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [treg]
  · have ne (a : Nat) (ha : a < 16) : v ≠ treg a := (hv a ha).symm
    obtain n0 : v ≠ .v16 := ne 0 (by decide)
    obtain n1 : v ≠ .v17 := ne 1 (by decide)
    obtain n2 : v ≠ .v18 := ne 2 (by decide)
    obtain n3 : v ≠ .v19 := ne 3 (by decide)
    obtain n4 : v ≠ .v20 := ne 4 (by decide)
    obtain n5 : v ≠ .v21 := ne 5 (by decide)
    obtain n6 : v ≠ .v22 := ne 6 (by decide)
    obtain n7 : v ≠ .v23 := ne 7 (by decide)
    obtain n8 : v ≠ .v24 := ne 8 (by decide)
    obtain n9 : v ≠ .v25 := ne 9 (by decide)
    obtain n10 : v ≠ .v26 := ne 10 (by decide)
    obtain n11 : v ≠ .v27 := ne 11 (by decide)
    obtain n12 : v ≠ .v28 := ne 12 (by decide)
    obtain n13 : v ≠ .v29 := ne 13 (by decide)
    obtain n14 : v ≠ .v30 := ne 14 (by decide)
    obtain n15 : v ≠ .v31 := ne 15 (by decide)
    simp [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]
  · simp [State.setV]

theorem saveK_ok (s : State) :
    WP isa (.block (save false)) s fun t =>
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ≠ .x10 → g ≠ .x11 → g ≠ .x14 → g ≠ .x15 → g ≠ .x16 → g ≠ .x17 → t.gpr g = s.gpr g) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold save saved
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil]
  refine ⟨fun p hp => ?_, fun g a b c d e f => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [a, b, c, d, e, f]
  · simp [State.write]

/-- The registers the key schedule's setup writes. -/
def ksaRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x14, .x15, .x16, .x17]

/-- The key schedule's globals for the call from `s`, entering the loop in `t`. -/
def kglob (s t : State) : KGlob := ⟨s.gpr .x0, (s.gpr .x1).toNat, s.mem, t⟩

/-- An entry of `Vector.ofFn f`, for any length: with the length a numeral,
the kernel builds the vector to compare the forms of the goal. -/
theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) {k : Nat} (hk : k < n) (d : α) :
    (Vector.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Vector.getD, hk]

theorem ident_get {k : Nat} (hk : k < 256) :
    (Vector.ofFn fun i : Fin 256 => BitVec.ofNat 8 i.val).getD (BitVec.ofNat 8 (0 + k)).toNat 0 =
      BitVec.ofNat 8 k := by
  rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, getD_ofFn _ hk]

theorem scheduleSetup_eq : scheduleSetup = save false ++ (constants ++ (identCode ++
    ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0,
      .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr))) := by
  rw [← identCode_eq]; simp only [scheduleSetup, List.append_assoc]

theorem tailK_ok (c : State) :
    WP isa (.block ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0,
      .addImm .x .x5 .x1 0, .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr)) c fun t =>
      t.v (dq 0) = 0 ∧ t.v si = 0 ∧ (∀ v, v ≠ .v0 → v ≠ .v4 → t.v v = c.v v) ∧
      t.gpr .x7 = c.gpr .x0 ∧ t.gpr .x5 = c.gpr .x1 ∧ t.gpr .x4 = 16#64 ∧ t.gpr .x8 = 0#64 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → t.gpr r = c.gpr r) ∧
      t.mem = c.mem ∧ t.rd = c.rd ∧ t.wr = c.wr ∧ t.sp = c.sp := by
  have d0 : dq 0 = .v0 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, s4]
  refine ⟨fun v a b => by simp [a, b], fun r a b c d => by simp [a, b, c, d], ?_⟩
  simp [State.write, State.setV]

theorem ksaSetup_ok {s : State} (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa (.block scheduleSetup) s fun t =>
      (kglob s t).Ok ∧ KsaInv (kglob s t) 0 0 t ∧
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r) ∧ t.v .v14 = s.v .v14 ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [scheduleSetup_eq, WP.block_append_iff]
  refine WP.mono (saveK_ok s) fun a ⟨asv, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok a) fun b ⟨bc', bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ident_ok bc') fun c ⟨ct, cv, cg, cm, crd, cwr, csp⟩ => ?_
  refine WP.mono (tailK_ok c) fun t ⟨tj, tsi, tv, t7, t5, t4, t8, tg, tm, trd, twr, tsp⟩ => ?_
  have hL1 := hL.1
  obtain gk : ∀ r, r ∉ ksaRegs → t.gpr r = s.gpr r := fun r hr => by
    obtain n : ∀ g ∈ ksaRegs, r ≠ g := fun g hg e => hr (e ▸ hg)
    rw [tg r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)), cg,
      bg r (n _ (by decide)) (n _ (by decide)),
      ag r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide))
        (n _ (by decide))]
  obtain t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide)
  obtain t1 : t.gpr .x1 = s.gpr .x1 := gk _ (by decide)
  obtain tvt : ∀ q < 16, t.v (treg q) = laneNums q := fun q hq => by
    rw [tv _ ((show NotTable .v0 by decide) q hq) ((show NotTable .v4 by decide) q hq), ct q hq]
  obtain tcon : Consts t := bc'.congr fun r hr => by
    rw [tv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      cv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain tb : ∀ k < 256, tbyte t.v k = BitVec.ofNat 8 k := fun k hk => by
    rw [tbyte, tvt _ (by omega_using [hk]), laneNums, vbyte_ofVBytes _ (by omega_using [])]
    congr 1; omega_using []
  obtain keep : ∀ v, v ≠ .v0 → v ≠ .v4 → NotTable v → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 →
      v ≠ .v11 → v ≠ .v12 → v ≠ .v13 → t.v v = s.v v := fun v h0 h4 ht h7 h8 h9 h10 h11 h12 h13 => by
    rw [tv v h0 h4, cv v ht, bv v h7 h8 h9 h10 h11 h12 h13, av]
  obtain hok : (kglob s t).Ok := by
    refine ⟨hL.1, hL.2, t0, ?_, ?_⟩
    · show t.gpr .x1 = _
      rw [t1]; simp [kglob]
    · show InRegions (t.rd ++ t.wr) _ _
      rw [trd, twr, crd, cwr, brd, bwr, ard, awr]; exact hk
  refine ⟨hok, ?_, fun p hp => ?_, gk, keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), by rw [tm, cm, bm, am], by rw [trd, crd, brd, ard],
    by rw [twr, cwr, bwr, awr], by rw [tsp, csp, bsp, asp]⟩
  · exact {
      consts := tcon
      table := fun k hk => by rw [tb k hk]; exact (ident_get hk).symm
      j := by rw [tj, Nat.add_zero, schedule_zero]; decide
      si := by rw [tsi, tb 0 (by decide)]; rfl
      x7 := by rw [t7, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; simp [kglob]
      x5 := by
        rw [t5, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        simp [kglob]
      x8 := by rw [t8]
      x4 := by rw [t4]
      gpr := fun _ _ _ _ _ _ => rfl
      vkept := fun _ _ => rfl
      mem := by rw [tm, cm, bm, am]; rfl
      rd := rfl
      wr := rfl
      sp := rfl }
  · have ⟨h6, h7⟩ : p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by revert p; decide
    have ⟨h4, h5, h8⟩ : p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x8 := by revert p; decide
    rw [tg _ h4 h5 h7 h8, cg, bg _ h6 h7, asv p hp]

end VG.Proof.Rc4.AArch64

end

end


/-!
# The key schedule

`init_ok`: `vg_rc4_init` checks the key length, and for a valid one leaves
the key schedule with both indices zero at `ctx`, preserving the low halves
of `v8`–`v15`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ctxRegs_ok (a : State) :
    WP isa (.block [.addImm .x .x0 .x2 0, .movz .x .x9 255 0]) a fun b =>
      b.gpr .x0 = a.gpr .x2 ∧ b.gpr .x9 = 255#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x9 → b.gpr r = a.gpr r) ∧
      b.v = a.v ∧ b.mem = a.mem ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  rrun
  refine ⟨fun r h0 h9 => by simp [h0, h9], ?_⟩
  simp [State.write]

theorem zeros_ok {b : State} (hp : InRegions b.wr (b.gpr .x0) 258) :
    WP isa (.block [.movz .w .x6 0 0, .strb .x6 .x0 256, .strb .x6 .x0 257, .movz .w .x0 0 0]) b
      fun c => c.mem = (b.mem.write (b.gpr .x0 + 256#64) 1 0).write (b.gpr .x0 + 257#64) 1 0 ∧
        c.gpr .x0 = 0#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x6 → c.gpr r = b.gpr r) ∧ c.v = b.v ∧
        c.rd = b.rd ∧ c.wr = b.wr ∧ c.sp = b.sp := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  obtain hz : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 0#16))) =
    0#8 := by decide
  rrun [State.store, h256, h257]
  refine ⟨by rw [hz], fun r a b => by simp [a, b], by simp [State.write]⟩

theorem ksaFinish_ok {g : KGlob} {u : State} (h : KsaInv g 256 0 u)
    (hp : InRegions u.wr (u.gpr .x2) 258) :
    WP isa (.block scheduleFinish) u fun t =>
      t.gpr .x0 = 0#64 ∧
      contextAt t.mem (u.gpr .x2) = { table := (schedulePrefix g.key 256).1, i := 0, j := 0 } ∧
      (∀ p ∈ saved false, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved false, p.1 ≠ v) → t.v v = u.v v) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  unfold scheduleFinish
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ctxRegs_ok u) fun a ⟨a0, a9, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff, storeTable_eq]
  obtain a8 : a.gpr .x8 = BitVec.ofNat 64 256 := by rw [ag _ (by decide) (by decide)]; exact h.x8
  obtain hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  obtain hpa' : InRegions a.wr (a.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpa
  refine WP.mono (storeN_ok (by decide) a8 a9 hpa' (Nat.le_refl 16))
    fun b ⟨brow, _, bv, bg, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  obtain b0 : b.gpr .x0 = a.gpr .x0 := bg _ (by decide) (by decide)
  refine WP.mono (zeros_ok (by rw [bwr, b0]; exact hpa)) fun c ⟨cm, c0, cg, cv, crd, cwr, csp⟩ => ?_
  refine WP.mono (restore_ok false c) fun t ⟨tsv, tv, tg, tm, trd, twr, tsp⟩ => ?_
  obtain hT : TableIn a 256 (schedulePrefix g.key 256).1 := fun k hk => by
    rw [show tbyte a.v = tbyte u.v by rw [av]]; exact h.table k hk
  refine ⟨?_, ?_, fun p hp => ?_, fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [tg, c0]
  · rw [tm, cm, b0, a0, context_finish, ← a0, stored_table (by decide) hT brow]
  · have ⟨n0, n6, n7, n9⟩ : p.2 ≠ .x0 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧ p.2 ≠ .x9 := by revert p; decide
    rw [tsv p hp, cg _ n0 n6, bg _ n6 n7, ag _ n0 n9]
  · rw [tv v hv, cv, bv, av]
  · rw [trd, crd, brd, ard]
  · rw [twr, cwr, bwr, awr]
  · rw [tsp, csp, bsp, asp]

theorem savedK_v : ∀ r ∈ preservedV, r = .v14 ∨ r = .v15 ∨ ∃ p ∈ saved false, p.1 = r := by decide

theorem savedK_kept : ∀ p ∈ saved false, p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧
    p.2 ≠ .x8 := by decide

theorem initValid_ok (s : State) (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa initValid s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat), i := 0, j := 0 } ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold initValid
  refine WP.seq (WP.mono (ksaSetup_ok hL hk)
    fun t ⟨hok, hi, tsv, tg, t14, t15, _, _, twr, _⟩ => ?_)
  refine WP.seq (WP.mono (ksaLoop_ok hok 16 ⟨0, rfl, rfl, by decide, hi⟩) fun u hu => ?_)
  obtain u2 : u.gpr .x2 = s.gpr .x2 := by
    rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  obtain hpu : InRegions u.wr (u.gpr .x2) 258 := by
    rw [hu.wr, u2]; show InRegions t.wr _ _; rw [twr]; exact hp
  refine WP.mono (ksaFinish_ok hu hpu) fun w ⟨w0, wc, wsv, wv, _, _, _⟩ => ?_
  refine ⟨w0, ?_, fun r hr => ?_⟩
  · rw [← u2, wc, keySchedule_eq]; rfl
  · have hn : ∀ p ∈ saved false, p.1 ≠ .v14 ∧ p.1 ≠ .v15 := by decide
    rcases savedK_v r hr with rfl | rfl | ⟨p, hp, rfl⟩
    · rw [wv _ fun p hp => (hn p hp).1, hu.vkept _ (by decide)]; exact congrArg _ t14
    · rw [wv _ fun p hp => (hn p hp).2, hu.vkept _ (by decide)]; exact congrArg _ t15
    · obtain ⟨a4, a5, a6, a7, a8⟩ := savedK_kept p hp
      rw [wsv p hp, hu.gpr _ a4 a5 a6 a7 a8]
      exact tsv p hp

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = 0#64 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa VG.Impl.Rc4.AArch64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
      | .ok ctx => t.gpr .x0 = 0#64 ∧ contextAt t.mem (s.gpr .x2) = ctx
      | .error .invalidKeyLength => t.gpr .x0 = 1#64) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain hcheck : WP isa (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x4 = (s.gpr .x1 - 1#64) >>> 8 := by rrun
  unfold VG.Impl.Rc4.AArch64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htv, ht0, ht1, ht2, ht4⟩ := ht
  let good := 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256
  obtain hcond : isa.eval (.nonzero .x .x4) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht4, BitVec.ofNat_eq_ofNat, bne]
    apply congrArg some
    by_cases hg : good
    · have hz := (valid_length (s.gpr .x1)).mpr hg
      rw [hz, beq_self_eq_true]
      simp only [hg, not_true_eq_false, decide_false, Bool.not_true]
    · have hn : (s.gpr .x1 - 1#64) >>> 8 ≠ 0#64 := fun hz => hg ((valid_length _).mp hz)
      rw [beq_eq_false_iff_ne.mpr hn]
      simp only [hg, not_false_eq_true, decide_true, Bool.not_false]
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
    exact fun r _ => by rw [htv]
  · have hg : good := by
      obtain hnn := of_decide_eq_false hy
      exact Classical.not_not.mp hnn
    change 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    obtain hpt : InRegions t.wr (t.gpr .x2) 258 := by rw [htw, ht2]; exact hp
    obtain hkt : InRegions (t.rd ++ t.wr) (t.gpr .x0) (t.gpr .x1).toNat := by
      rw [htr, htw, ht0, ht1]; exact hk
    obtain hlt : 0 < (t.gpr .x1).toNat ∧ (t.gpr .x1).toNat ≤ 256 := by rw [ht1]; omega_using [hg]
    refine WP.mono (initValid_ok t hlt hpt hkt) fun u ⟨u0, uc, uv⟩ => ?_
    refine ⟨⟨u0, ?_⟩, fun r hr => by rw [uv r hr, htv]⟩
    rw [← ht2, uc, htm, ht0, ht1]

end VG.Proof.Rc4.AArch64

end

end


@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified AArch64.target VG.Impl.Rc4.AArch64.init
    (Spec.Rc4.initContract AArch64.abi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    sig_pre [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs] at hs
    obtain ⟨hrd, hwr, _⟩ := hs
    obtain hp : InRegions s.wr (s.gpr .x2) 258 := by
      refine ⟨⟨s.gpr .x2, 258⟩, ?_, ?_⟩
      · rw [hwr]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    obtain hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat := by
      refine ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ?_, ?_⟩
      · rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _)
      · simp [Region.Contains]
    obtain hw := WP.gprs (rs := preserved) (init_ok s hp hk) (by lit_decide) (by rfl)
    obtain ⟨tr, t, he, ⟨hpost, hv⟩, hregs⟩ := hw
    refine ⟨tr, t, he, ⟨hregs, Exec.sp he, hv⟩, ?_⟩
    sig_post [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs]
    cases hc : Spec.Rc4.init (Spec.Rc4.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
    | ok ctx =>
      rw [hc] at hpost
      dsimp only at hpost ⊢
      exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
    | error err =>
      cases err
      rw [hc] at hpost
      dsimp only at hpost ⊢
      rw [hpost]
      rfl
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hpub he₁ he₂
    sig_pub [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs] at hpub
    obtain ⟨hsp, h0, h1, h2⟩ := hpub
    obtain hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
      refine ⟨hsp, fun r hr => ?_⟩
      simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption
    exact init_ct s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hagree he₁ he₂
  · sig_implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, AArch64.abi,
      AArch64.argRegs]
      [initSat] using initSat

/-- `init`, with what it leaves cleared, meets the same contract. -/
theorem initCleared_verified : Verified AArch64.target initCleared (Spec.Rc4.initContract AArch64.abi) :=
  Clears.Verified.withClears init_verified (by decide)

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Rc4.AArch64.initCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Rc4.AArch64.Fn.init
      (Spec.Rc4.initContract AArch64.abi) 32 :=
  ⟨Proof.Rc4.AArch64.initCleared_verified,
    Proof.Rc4.AArch64.initCleared_noResidue _⟩

end VG.Proof.Rc4.AArch64
