module

public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.X25519.RISCV64.Invert
public import VerifiedGarbage.Proof.X25519.RISCV64.Main
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
import VerifiedGarbage.Proof.X25519.RISCV64.Freeze
public import VerifiedGarbage.Proof.X25519.RISCV64.Setup
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.X25519.RISCV64.R64
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.RISCV64.R64.CT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X25519 on RISC-V, 64-bit limbs: verified

The inversion, as `Proof/X25519/RISCV64/Invert.lean` proves it: `invert`
computes `z^(p-2)` into `R` for the element `z` at `Z2` by square-and-multiply
over the bits of `p - 2` from 254 down to 0 (`invert_ok`).

Then the whole function: `vg_x25519` writes `X25519(k, u)` to `out`
(`x25519_correct`), against `Proof/X25519/RISCV64/Main.lean`'s contract,
with that file's decoding, bits and final reduction, and meets the shared
contract of `Spec/X25519/Contract.lean`: the code calls no function and
writes only caller-saved registers (`WP.keep`), so the ABI's obligations hold
of every execution.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.R64

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64.R64
open VG.Impl.X25519.RISCV64 (X1 X2 Z2 X3 Z3 R BITS one)
open VG.Spec.X25519 (P Fe bytesAt)

section
variable {b : Addr}

/-! ## The inversion -/

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : Addr) (sI : State) (a : BitVec 64) (v : Nat → Fe) (n : Nat) (s : State) :
    Prop where
  cur : Cur b sI a (BitVec.ofNat 64 n) IQ (invV v n) s

theorem Cur.congr {s0 s : State} {a c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.t2, h.t1, (h.slots.mono hq).congr hv⟩

/-- `addi a2, t1, -d`, and the branch on `a2 = 0`. -/
theorem cmp_ok {s0 s : State} {a : BitVec 64} {qs : List Nat} {v : Nat → Fe} {m d : Nat}
    (hm : m < 255) (hd : d < 255) (h : Cur b s0 a (BitVec.ofNat 64 m) qs v s) :
    WP isa (.block [.addi .a2 .t1 (-d)]) s fun s' => Cur b s0 a (BitVec.ofNat 64 m) qs v s' ∧
      isa.eval (.zero .a2) s' = some (decide (m = d)) := by
  refine wp_subi (by omega_using [hd]) fun s1 u1 => WP.block_nil ⟨h.next (u1.rest (by decide))
    (by rw [u1.mem]; exact Frame.refl _ _) (by rw [u1.mem]; exact h.slots), ?_⟩
  rw [eval_zero, u1.gpr, h.t1, sub_beq (by omega_using [hm]) (by omega_using [hd])]

theorem invStep_ok {sI : State} {a : BitVec 64} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI a v n s) :
    WP isa invStep s fun s' => InvInv b sI a v (n - 1) s' ∧ (s'.gpr .t1 != 0) = decide (n - 1 ≠ 0) := by
  obtain ⟨hcur⟩ := h
  have hb := pbits (n - 1) (by omega_using [hn'])
  have he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (wp_subi (by decide) fun s1 u1 => WP.block_nil ?_)
  have h1 : Cur b sI a (BitVec.ofNat 64 (n - 1)) IQ (invV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hcur.t2], ?_, by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr, hcur.t1, ofNat_sub_one hn (by omega_using [hn'])]
  refine WP.seq (WP.mono (opMul (o := R) (x := R) (y := R) (by decide) (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  -- After the square.
  have hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := IQ) (by decide) hsq
  refine WP.seq (WP.mono (cmp_ok (d := 4) (by omega_using [hn']) (by decide) h2') fun s3 ⟨h3, hz3⟩ => ?_)
  refine WP.seq (WP.mono (Q := Cur b sI a (BitVec.ofNat 64 (n - 1)) IQ (invV v (n - 1))) ?_ fun s4 h4 =>
    WP.block_nil ⟨⟨h4⟩, by rw [h4.t1, ofNat_ne_zero (by omega_using [hn'])]⟩)
  refine WP.ite _ hz3 (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
  · have h4 : n - 1 = 4 := by simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 4 := by simpa using hf
    refine WP.seq (WP.mono (cmp_ok (d := 2) (by omega_using [hn']) (by decide) h3) fun s4 ⟨h4', hz4⟩ => ?_)
    refine WP.ite _ hz4 (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
    · have h2 : n - 1 = 2 := by simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h2 : n - 1 ≠ 2 := by simpa using hf
      refine WP.mono (opMul (o := R) (x := R) (y := Z2) (by decide) (by decide) (by decide) (by decide) h4')
        fun s5 h5 => h5.congr (by decide) fun q _ => ?_
      by_cases hq : q = R
      · subst hq
        rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
          iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega), ← VG.Proof.X25519.pw_mul,
          VG.Proof.X25519.pw_one]
      · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]

theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .t2 = a) :
    WP isa Impl.X25519.RISCV64.R64.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 480 := rfl
  unfold Impl.X25519.RISCV64.R64.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.a1, .a2] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine sw0_ok hc2 (d := R) (by decide) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 7) (by decide) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.a1, .a2, .t1] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 8, limb s5.mem b R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, toNat_lo32, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf5 : Frame [⟨b + BitVec.ofNat 64 R, 32⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) ((s2.gpr .a1).setWidth 32)
      (Offset.contains b (d := R) (n := 32 / 8) (e := R) (k := 32) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩⟩
  have hS5 : SlotsOk s5.mem b IQ (invV v 255) := by
    have hZ2 : Z2 = 64 := rfl
    have hX2 : X2 = 32 := rfl
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e := limb_frame (o := Z2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hZ2, hR, hk])) (by omega_using [hZ2, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, invV, upd_of_ne _ _ (by decide)]; exact hS Z2 (by decide)
    · rw [FS, V, val32_congr hlimb, invV, upd_self, p255, VG.Proof.X25519.pw_zero]
      rfl
    · have e := limb_frame (o := X2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX2, hR, hk])) (by omega_using [hX2, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, invV, upd_of_ne _ _ (by decide)]; exact hS X2 (by decide)
  have h255 : InvInv b s5 a v 255 s5 :=
    ⟨⟨hc5, Stp.refl _ _, by rw [hr5.gpr _ (by decide), h0], u5.gpr, hS5⟩⟩
  refine WP.mono (Q := InvInv b s5 a v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s5 a v m s') ?_ 255 s5 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩

/-! ## The whole function -/

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .t2 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have hr2 : Rest [.t0] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e11 : s2.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

end

theorem x25519_correct {s : State} (hp : XPre s) :
    WP isa x25519 s fun s' => x25519RISCV64.post s s' := by
  have hB : BITS = 608 := rfl
  have hsc_in : (⟨s.gpr .a1, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519
  have hsub : Region.Sub ⟨wsBase s, 2048⟩ ⟨s.gpr .a3, 4096⟩ := by
    have := wsBase_sub s (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .a1 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    (hp.sc_ws.sub_right hsub)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h0, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h0 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) hc5 hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : Stp (wsBase s) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have h3' : s6.gpr .a0 = s.gpr .a0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), hr1.gpr _ (by decide)]
  have hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  have hc6 : Ctx (wsBase s) s6 := hc5.of_rest hr6 (by decide)
  refine WP.mono (freeze_ok hc6 h3' (by rw [hwr6, hp.wr]; simp) (hp.out_ws.sub_right hsub).symm)
    fun s7 ⟨hbytes, _, _⟩ => ?_
  -- The result.
  show bytesAt s7.mem _ 32 = _
  rw [hbytes, VG.Proof.X25519.x25519_eq]
  -- The scalar, as read by `bits`.
  have hk : bytesAt s1.mem (s.gpr .a1) 32 = bytesAt s.mem (s.gpr .a1) 32 :=
    bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  have e6 : FS s6.mem (wsBase s) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
  change VG.Spec.X25519.encodeUCoordinate (FS s6.mem (wsBase s) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
    uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end

section

open VG VG.RISCV64

theorem x25519_ok (s : State) (hs : x25519RISCV64.pre s) :
    ∃ t s', Exec isa Impl.X25519.RISCV64.R64.x25519 s t s' ∧ abiPreserved s s' ∧
      x25519RISCV64.post s s' := by
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (x25519_correct (XPre.of hs)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

theorem x25519_ct' :
    ConstantTime isa x25519RISCV64.pre x25519RISCV64.pub Impl.X25519.RISCV64.R64.x25519 :=
  x25519_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified RISCV64.target Impl.X25519.RISCV64.R64.x25519 (Spec.X25519.x25519Contract RISCV64.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    contract_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.RISCV64.x25519RISCV64,
      RISCV64.abi, RISCV64.argRegs] [Proof.X25519.RISCV64.R64.x25519Sat]
      using Proof.X25519.RISCV64.R64.x25519Sat)

end

end VG.Proof.X25519.RISCV64.R64
