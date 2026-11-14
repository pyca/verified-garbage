module
public import VerifiedGarbage.Proof.Rc4.AArch64.Prga
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Rc4.AArch64.ApplySetup
import VerifiedGarbage.Proof.Rc4.AArch64.Consts
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate

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
