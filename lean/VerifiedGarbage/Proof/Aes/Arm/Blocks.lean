import VerifiedGarbage.Proof.Aes.Arm.Ecb
import VerifiedGarbage.Proof.Aes.Arm.Ctr32

/-!
# AES on whole blocks on ARMv7: the whole functions

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` are `blocks` around
`encrypt2` and `decrypt2`, and are proven at once, for any transformation of
two blocks with `CryptOk`: the prologue saves the callee-saved registers
(as `vg_aes_ctr32`'s does, `Ctr32.lean`), stores `n` in its slot and
bitslices the round keys (`Keys.lean`); the groups (`Ecb.lean`) do the
rest; the epilogue restores the registers.
-/

namespace VG.Proof.Aes

open VG.Arm in
/-- 32-bit ARM contract for `vg_aes_encrypt_blocks(schedule = r0, rounds = r1,
data = r2, n = r3, scratch = [sp])` (and `vg_aes_decrypt_blocks`, with `f` the
inverse cipher): replaces each of the `n` blocks at `data` with `f rounds w`
of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and the argument on the stack (4
bytes at `sp`), and read and write `data` (`16 n` bytes) and `scratch` (2048
bytes, whose contents on exit are unspecified). These may not overlap each
other, and none may wrap around the end of the (32-bit) address space.
`rounds` is 10, 12 or 14. The pointers, `rounds` and `n` are public; the key
schedule and the data are secret. -/
def blocksArm (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 2048⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    data.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 2048 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      (Spec.Aes.statesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).map
        (f (s.gpr .r1).toNat
          (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm.Ecb

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp
  wp_ldr wp_str wp_ldrSp)

section
variable (s₀ : State)

abbrev scP : BitVec 32 := s₀.gpr .r0
abbrev dP : BitVec 32 := s₀.gpr .r2
abbrev nB : Nat := (s₀.gpr .r3).toNat
abbrev bP : BitVec 32 := stackArg s₀ 0
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (scP s₀), 240⟩, argR s₀]
  wr : s₀.wr = [⟨State.addr (dP s₀), 16 * nB s₀⟩, ⟨State.addr (bP s₀), 2048⟩]
  dSD : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (dP s₀), 16 * nB s₀⟩
  dSS : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (bP s₀), 2048⟩
  dDS : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ ⟨State.addr (bP s₀), 2048⟩
  dDA : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ (argR s₀)
  dSA : Region.Disjoint ⟨State.addr (bP s₀), 2048⟩ (argR s₀)
  fitS : (scP s₀).toNat + 240 ≤ 2 ^ 32
  fitD : (dP s₀).toNat + 16 * nB s₀ ≤ 2 ^ 32
  fitB : (bP s₀).toNat + 2048 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rounds : (s₀.gpr .r1).toNat = 10 ∨ (s₀.gpr .r1).toNat = 12 ∨ (s₀.gpr .r1).toNat = 14

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksArm f).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem arg_in {s : State} (hr : argR s ∈ s.rd) : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
  ⟨argR s, List.mem_append_left _ hr, by simp [Region.Contains]⟩

/-- The stack argument is as on entry. -/
theorem stackArg_frame {s s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsp : s'.sp = s.sp)
    (hd : ∀ r ∈ rs, Region.Disjoint (argR s) r) : stackArg s' 0 = stackArg s 0 := by
  simp only [stackArg, stackArgAddr, hsp]
  exact hf.readW (by simp [Region.Contains, stackArgAddr]) hd (by decide)

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n (4 * n) F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (show 16 * j + t < 4 * (4 * n) by omega),
    show (16 * j + t) / 16 = j by omega, show (16 * j + t) % 16 = t by omega, getD_eq _ ht]

/-! ## The key loop, counting in the low 4 bits of `lr` -/

theorem and15 {N j : Nat} (hj : j < 16) (hN : 16 * N + 16 ≤ 2 ^ 32) :
    BitVec.ofNat 32 (16 * N + j) &&& 15 = BitVec.ofNat 32 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {N : Nat} (hN : 16 * N + 16 ≤ 2 ^ 32) : BitVec.ofNat 32 (16 * N) >>> 4 = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

theorem blocksKeyBody_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {j : Nat} {s : State}
    (hi : KInv s₀ b sc R w j s) (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + j + 1)) :
    WP isa (.block blocksKeyBody) s fun s' =>
      (j = 0 ∧ Arm.eval .ne s' = some false ∧ KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N)) ∨
      (0 < j ∧ Arm.eval .ne s' = some true ∧ KInv s₀ b sc R w (j - 1) s' ∧
        s'.gpr .lr = BitVec.ofNat 32 (16 * N + (j - 1) + 1)) := by
  have hR := hk.rounds
  have hjR := hi.hj
  simp only [blocksKeyBody]
  refine keyFront_ok hk hi fun s₃ hr12 hkp hlr₃ hkeep₃ hrd hwr hsp hfr hkeys => ?_
  simp only [blocksKeyStep]
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_imm (by decide)) fun s₅ u₅ =>
    wp_sub (op2_imm (by decide)) fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_and (op2_imm (by decide))
    fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  have hlr₈ : s₈.gpr .lr = BitVec.ofNat 32 (16 * N + j) := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hlr₃,
      hlr]
    bv_omega
  have hev : Arm.eval .ne s₈ = some (!(BitVec.ofNat 32 j == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    simp only [Arm.eval, z₈, e0, u₇.gpr]
    rw [show s₆.gpr .lr = BitVec.ofNat 32 (16 * N + j) by
      rw [← hlr₈, f₈.gpr, u₇.other _ (by decide)], and15 (by omega) hN]
  have hkeep : ∀ r, r ∉ keyWrites → s₈.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    have h5 : r ≠ t0 := fun h => h1 (h ▸ by decide)
    rw [f₈.gpr, u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.other _ h2, hkeep₃ r hr]
  have m₈ : s₈.mem = s₃.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₈ : s₈.rd = s₀.rd := by rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, hrd]
  have wr₈ : s₈.wr = s₀.wr := by rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, hwr]
  have sp₈ : s₈.sp = s₀.sp := by rw [f₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, hsp]
  have kp₈ : s₈.gpr kp = keyAddr b R j - 32 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), hkp]
  have r12₈ : s₈.gpr .r12 = sc + BitVec.ofNat 32 (16 * j) - 16 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hr12]
  rw [← m₈] at hfr hkeys
  by_cases h0 : j = 0
  · subst h0
    exact .inl ⟨rfl, hev.trans (by decide), ⟨kp₈, rd₈, wr₈, sp₈, hkeep, hfr,
      fun i hiR => hkeys i (by omega) hiR⟩, by rw [hlr₈]; rfl⟩
  · have hne : BitVec.ofNat 32 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine .inr ⟨by omega, hev.trans (by simpa using hne),
      ⟨by omega, ?_, ?_, rd₈, wr₈, sp₈, hkeep, hfr, fun i hi' hiR => hkeys i (by omega) hiR⟩,
      by rw [hlr₈, show 16 * N + (j - 1) + 1 = 16 * N + j by omega]⟩
    · rw [r12₈]; bv_omega
    · rw [kp₈]; exact keyAddr_pred b hk.rounds (by omega) hi.hj

theorem blocksKeyLoop_ok {s₀ : State} {b sc : BitVec 32} {R N : Nat} {w : List Byte}
    (hk : KSetup s₀ b sc R w) (hN : 16 * N + 16 ≤ 2 ^ 32) {s : State} (hi : KInv s₀ b sc R w R s)
    (hlr : s.gpr .lr = BitVec.ofNat 32 (16 * N + R + 1)) :
    WP isa (.loop (.block blocksKeyBody) .ne) s fun s' =>
      KDone s₀ b R w s' ∧ s'.gpr .lr = BitVec.ofNat 32 (16 * N) := by
  refine WP.loop (M := isa)
    (fun n s => KInv s₀ b sc R w n s ∧ s.gpr .lr = BitVec.ofNat 32 (16 * N + n + 1))
    (fun n s hs => ?_) R s ⟨hi, hlr⟩
  refine WP.mono (blocksKeyBody_ok hk hN hs.1 hs.2) fun s' h => ?_
  rcases h with ⟨_, hev, hd, hl⟩ | ⟨hn, hev, hi', hlr'⟩
  · exact .inl ⟨hev, hd, hl⟩
  · exact .inr ⟨hev, n - 1, by omega, hi', hlr'⟩

theorem correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) {s₀ : State} (hp : Pre s₀) :
    WP isa (blocks crypt2) s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksArm f).post s₀ s' := by
  have hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hfit := hp.fitB
  have hwS : (⟨State.addr (bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwD : (⟨State.addr (dP s₀), 16 * nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hrS : (⟨State.addr (scP s₀), 240⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := bP s₀
  let B := State.addr b
  let n := nB s₀
  let D := State.addr (dP s₀)
  have n16 : 16 * n < 2 ^ 64 := by have := hp.fitD; omega
  have argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨B, lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  have argD : ∀ {x lx : Nat}, x + lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨B + BitVec.ofNat 64 x, lx⟩ :=
    fun h => (hp.dSA.sub_left (sub_scr _ h)).symm
  -- The prologue.
  unfold blocks
  refine WP.seq ?_
  simp only [blocksPrologue, blocksKeySetup, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) rfl (arg_in hrA) fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ :=
    save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have sv₂' : Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  have f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  have hb₂ : s₂.gpr .r12 = b := by rw [g₂, hb₁]
  have hscr₂ : (⟨B, 2048⟩ : Region) ∈ s₂.wr := by rw [wr₂, u₁.wr]; exact hwS
  -- The key loop's setup.
  have r0₂ : s₂.gpr .r0 = scP s₀ := by rw [g₂, u₁.other _ (by decide)]
  have r1₂ : s₂.gpr .r1 = s₀.gpr .r1 := by rw [g₂, u₁.other _ (by decide)]
  have r2₂ : s₂.gpr .r2 = dP s₀ := by rw [g₂, u₁.other _ (by decide)]
  have r3₂ : s₂.gpr .r3 = s₀.gpr .r3 := by rw [g₂, u₁.other _ (by decide)]
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide))
    fun s₄ u₄ => wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ =>
    wp_add (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₆' u₆' =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆'.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆'.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆'.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆'.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂']
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (scP s₀)) (16 * (R + 1))
  have f₀₇ : Frame [⟨B, 2048⟩] s₀.mem s₇.mem := by
    rw [m₇]
    exact f₀₂.sub fun r hr => ⟨⟨B, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hk : KSetup s₇ b (scP s₀) R w :=
    { scr := by rw [wr₇]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₇]; exact hrS)
      fitS := hp.fitS
      sep := hp.dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₇.bytes (R := ⟨State.addr (scP s₀), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega)).symm
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dSS }
  have hi₇ : KInv s₇ b (scP s₀) R w R s₇ :=
    { hj := Nat.le_refl _
      r12 := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), r0₂, u₃.other _ (by decide), r1₂, shl4]
      kp := by
        rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hb₂]
        simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  have hN : 16 * n + 16 ≤ 2 ^ 32 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have hD := hp.fitD
    simp only [n, nB] at hc hD
    have hz : State.addr (dP s₀) = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [VG.Proof.MdStream.Arm.addr_toNat]; show _ = 0; omega
    refine hp.dDS (State.addr (bP s₀)) ?_ (by
      show (State.addr (bP s₀) - State.addr (bP s₀)).toNat + 1 ≤ 2048; simp)
    show (State.addr (bP s₀) - State.addr (dP s₀)).toNat + 1 ≤ 16 * nB s₀
    have e : State.addr (bP s₀) - 0 = State.addr (bP s₀) := by bv_omega
    rw [hz, e, VG.Proof.MdStream.Arm.addr_toNat]
    have := (bP s₀).isLt
    simp only [nB]
    omega
  have lr₇ : s₇.gpr .lr = BitVec.ofNat 32 (16 * n + R + 1) := by
    rw [u₇.other _ (by decide), u₆'.gpr, u₆.gpr, u₅.gpr, u₅.other .r1 (by decide),
      u₄.other .r3 (by decide), u₄.other .r1 (by decide), u₃.other .r3 (by decide),
      u₃.other .r1 (by decide), r3₂, r1₂, shl4]
    simp only [n, nB, R]
    bv_omega
  have r8₇ : s₇.gpr .r8 = dP s₀ := by
    rw [u₇.gpr, u₆'.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), r2₂]
  -- The key loop.
  refine WP.seq (WP.mono (blocksKeyLoop_ok hk hN hi₇ lr₇) fun s₈ ⟨d₈, lr₈⟩ => ?_)
  have f₀₈ : Frame [⟨B, 2048⟩] s₀.mem s₈.mem :=
    f₀₇.trans (d₈.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨B, 2048⟩, by simp, keyArea_sub _⟩)
  have sp₈ : s₈.sp = s₀.sp := by rw [d₈.sp, sp₇]
  have arg₈ : stackArg s₈ 0 = b := stackArg_frame f₀₈ sp₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact argB (by omega)
  -- After the key loop.
  refine WP.seq ?_
  simp only [blocksKeyDone, List.cons_append, List.nil_append]
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, sp₈]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, d₈.rd, rd₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, d₈.wr, wr₇]
  have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, sp₁₀])
    (by rw [rd₁₀, wr₁₀]; exact arg_in hrA) fun s₁₁ u₁₁ => ?_
  have b₁₁ : s₁₁.gpr sb = b := by
    rw [u₁₁.gpr, m₁₀]
    have := arg₈
    simp only [stackArg, stackArgAddr, sp₈] at this
    exact this
  refine wp_mov (op2_lsr (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  have n₁₂ : s₁₂.gpr .r11 = s₀.gpr .r3 := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), lr₈,
      shr4 hN]
    simp [n]
  have n₁₃ : s₁₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * 0) := by
    rw [f₁₃.gpr, n₁₂]; simp only [n, nB, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have b₁₃ : s₁₃.gpr sb = b := by rw [f₁₃.gpr, u₁₂.other _ (by decide), b₁₁]
  have d₁₃ : s₁₃.gpr .r10 = dP s₀ + BitVec.ofNat 32 (32 * 0) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      d₈.keep _ (by decide), r8₇]
    simp
  have k₁₃ : s₁₃.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      d₈.kp]
    simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have m₁₃ : s₁₃.mem = s₈.mem := by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀]
  have hs : ESetup s₁₃ b (dP s₀) n R w :=
    { scr := by rw [wr₁₃]; exact hwS
      fit := hfit
      dat := by rw [wr₁₃]; exact hwD
      fitD := hp.fitD
      sep := hp.dDS
      rounds := hp.rounds
      keys := fun j hj => keyRel_congr (d₈.keys j hj) fun k hk => by
        rw [m₁₃, keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
          simp only [lastKey]; omega] }
  -- The data is as on entry.
  have data₁₃ : EcbInv s₀.mem s₁₃.mem D n (8 * 0) (ecbOut f s₀.mem D R w) := by
    intro i hi
    rw [ite_eq_right (by omega), m₁₃]
    refine f₀₈.bytes (R := ⟨D, 16 * n⟩) (fun r hr => ?_) (by simp only; omega) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dDS
  refine WP.seq (WP.mono (Q := EDone f s₀.mem s₁₃ b (dP s₀) n R w) ?_ fun s₁₄ gd => ?_)
  · have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    refine WP.ite (s₀.gpr .r3 == 0) (by simp only [Arm.eval, z₁₃, n₁₂, e0]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by
        simp only [beq_iff_eq] at h0; show (s₀.gpr .r3).toNat = 0; rw [h0]; rfl
      exact WP.block_nil ⟨b₁₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      exact groups_ok hcr hs ⟨by omega, d₁₃, n₁₃, k₁₃, b₁₃, rfl, rfl, rfl, Frame.refl _ _, data₁₃⟩
  -- The epilogue.
  have sv : Saved s₀ B s₁₄.mem := by
    intro i hi
    have c : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨slotA B (32 + i), 32 / 8⟩ r) →
        m'.readW (slotA B (32 + i)) 32 = m.readW (slotA B (32 + i)) 32 :=
      fun hf hd => hf.readW (Region.contains_self _ _) hd (by decide)
    rw [c gd.frame (slot_disj_regions hp.dDS (by omega) (by omega) (by omega)), m₁₃,
      c d₈.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact off_disjoint _ (by omega) (by omega) (by omega)), m₇, sv₂' i hi]
  have f₀₁₄ : Frame [⟨B, 2048⟩, ⟨D, 16 * n⟩] s₀.mem s₁₄.mem := by
    refine (f₀₈.mono fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))).trans ?_
    rw [← m₁₃]
    refine gd.frame.sub fun r hr => ?_
    simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨B, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨B, 2048⟩, by simp, sub_scr _ (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, gd.sp, sp₁₃])
    (by rw [gd.rd, gd.wr, rd₁₃, wr₁₃]; exact arg_in hrA) fun s₁₅ u₁₅ => ?_
  have b₁₅ : s₁₅.gpr .r12 = b := by
    rw [u₁₅.gpr]
    have := stackArg_frame f₀₁₄ (by rw [gd.sp, sp₁₃]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact argB (by omega)
      · exact hp.dDA.symm)
    simp only [stackArg, stackArgAddr, gd.sp, sp₁₃] at this
    exact this
  obtain ⟨s₁₆, h₁₆, rg₁₆, fR⟩ := restore_ok (s₀ := s₀) (by decide)
    (by rw [u₁₅.wr, gd.wr, wr₁₃]; exact hwS) hfit b₁₅ (by rw [u₁₅.mem]; exact sv)
  refine WP.of_runBlock ⟨s₁₆, h₁₆, rg₁₆, ?_⟩
  rw [u₁₅.mem] at fR
  show Spec.Aes.statesAt s₁₆.mem D n = _
  rw [statesAt_of_ecbInv (ecbInv_frame fR (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dDS.sub_right (Region.sub_prefix (by omega))) n16 gd.data)]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

theorem blocks_correct {crypt2 : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hcr : CryptOk crypt2 f) (s : State) (hs : (Proof.Aes.blocksArm f).pre s) :
    ∃ t s', Exec isa (blocks crypt2) s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksArm f).post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct hcr (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-! ## Constant time -/

/-- The initial taint: the pointers, `rounds`, `n` and the stack argument are
public; `r2` points at the data, and the stack argument at the scratch
buffer. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [0, 2048],
    bases := [(.r2, 0)], argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State}
    (h : (Proof.Aes.blocksArm f).pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨hp.dDS, fun _ h => h.elim, trivial⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitD; have := hp.fitB
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.dDA.symm
    · exact hp.dSA.symm
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₁ s₂ : State}
    (h₁ : (Proof.Aes.blocksArm f).pre s₁) (h₂ : (Proof.Aes.blocksArm f).pre s₂)
    (hpub : (Proof.Aes.blocksArm f).pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [dP, nB, bP, p2, p3, a0]
  · simp only [τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    rw [show k / 4 = 0 by omega]
    exact congrArg _ a0

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.cipher).pre
    (Proof.Aes.blocksArm Spec.Aes.cipher).pub encryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksArm Spec.Aes.invCipher).pre
    (Proof.Aes.blocksArm Spec.Aes.invCipher).pub decryptBlocks :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 0⟩, ⟨0, 2048⟩]

theorem encryptBlocks_verified :
    Verified Arm.target encryptBlocks (Spec.Aes.encryptBlocksContract Arm.abi) :=
  Verified.of_correct (blocks_correct encrypt2_cryptOk) encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.Ecb.sat)

theorem decryptBlocks_verified :
    Verified Arm.target decryptBlocks (Spec.Aes.decryptBlocksContract Arm.abi) :=
  Verified.of_correct (blocks_correct decrypt2_cryptOk) decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.Ecb.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.Ecb.sat)

end VG.Proof.Aes.Arm.Ecb
