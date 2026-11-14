module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZC.Loop
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemG
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGKs
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pow

/-!
# GCM encryption hashing each group from registers: the first group and the end

`midRestM_ok`: `StitchZH.midRest`, a message of 48 to 143 blocks after the
setup and the powers of 48 blocks, in place or out of place
(`Stitch.EPostM`): no block of the output is loaded back.

* The first group is a group of `StitchZC.grpC` with nothing between its
  rounds (`grpM_ok`), which leaves it in the copies (`CInv`), and
  `loopsC_ok` takes the groups after it.
* `finalC_ok`: with no block after the last group, the copies are hashed
  by `lastC`, the GHASH work of a last group's rounds (`hooks_run`,
  `gqC_ok`), and the counter and `Y` stored.
* `remC_ok`: the `r` blocks after the last group are a masked group, as in
  `StitchZH.remG_ok`, whose rounds hash the copies (`ksBatchC_ok`,
  `ksSelC_ok`, with `StitchZH.tailG_ok` after the rounds).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZC

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (nb nr kp pp cp yp cb dp cR yR pR bAddr blk ctb ciph sch hk y₀ ite_t ite_f addr_eq
  in_sub in_sub_int in_rdwr blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Proof.Gcm.X86_64.StitchZ (acc48 yNew48 FinOk48 gRegs48 store16Z_ok AInvM ReadyM aregs_ok)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZC (creg incAt gqC grpC lastC loopsC)
open VG.Proof.Aes.X86_64.VaesZ (four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block blockAt ghashFrom inc32)

/-! ## The GHASH work of a group's rounds, by itself -/

/-- The blocks after rounds 1 to `n` of a group, with no round between. -/
theorem hooks_run {nr : Nat} {w : List Byte} {g : Nat → List Instr} {G : List XReg} {Q : Nat → State → Prop}
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s') :
    ∀ n, n ≤ 9 → ∀ s, Keys nr w s → Q 1 s →
      WP isa (.block ((List.range n).flatMap fun i => g (i + 1))) s fun s' => Q (n + 1) s' ∧ ZFrame G s s'
  | 0, _, s, _, hQ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hQ, ZFrame.refl _ _⟩
  | n + 1, hn, s, hK, hQ => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (hooks_run hg n (by omega_using [hn]) s hK hQ) fun s₁ ⟨hQ₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (hg (n + 1) (by omega_using []) hn s₁ (ZFrame.of_keys hK f₁) hQ₁) fun s' ⟨hQ', f'⟩ =>
      ⟨hQ', f₁.trans f'⟩

/-- The 48 blocks whose products the hashing of a last group in the copies
adds: 32 of zero, and group `e - 1` of the output, `Y` added to its first. -/
abbrev lastX (s₀ : State) (e : Nat) (s : State) : Nat → Block :=
  padX 2 (fun i => ctb s₀ (16 * (e - 1) + i)) (fun l => s.zlane .xmm2 l)

/-- `Y` once the group in the copies is hashed: `GHASH` over the `e` groups. -/
theorem yLast {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    {s : State} (hI : CInv ix s₀ T e s) :
    yNew48 (lastX s₀ e s) T (fun _ => 0) =
      ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) := by
  have h1e := hI.one
  rw [hT _ (fun _ => 0) (fun _ _ _ => rfl), ghash_pad (hk s₀) (by decide) _ _ hI.y1, hI.y,
    show 48 - 16 * 2 = 16 from rfl, ← ghash_appendN]
  congr 3
  omega_using [h1e]

/-- What the GHASH work of a last group's rounds keeps, on the copies of
group `e - 1` (`QC`, for `lastX`). -/
abbrev QL (s₀ : State) (T : Nat → Nat → Nat → Block) (e : Nat) (s : State) : Nat → State → Prop :=
  QC s₀ T (lastX s₀ e s) (fun n => ctb s₀ (16 * (e + 0) - 16 + n)) (fun l => s.zlane .xmm2 l) true true 2

/-- `gqC_ok`, for the last group. -/
theorem gqLast {s₀ : State} {T : Nat → Nat → Nat → Block} {e : Nat} (h1e : 1 ≤ e) (s : State) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → QL s₀ T e s j t →
      WP isa (.block (gqC true true 2 j)) t fun t' => QL s₀ T e s (j + 1) t' ∧ ZFrame gRegs48 t t' :=
  gqC_ok (by decide) (padX_grp (g₀ := 2) (t := 0) rfl h1e _ true (by simp))
    (fun _ l hl => acc48_pad 2 _ _ T hl 4 (by omega_using [])) (fun _ => rfl)

/-- `QL` before the first round, from the invariant, in a state with its
copies, `Y` and working space. -/
theorem QL.start {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block} {e : Nat} {s t : State}
    (hI : CInv ix s₀ T e s) (hE : CEnv s₀ T t)
    (hcp : ∀ k < 4, ∀ l < 4, t.zlane (creg k) l = s.zlane (creg k) l)
    (h2 : ∀ l < 4, t.zlane .xmm2 l = s.zlane .xmm2 l) : QL s₀ T e s 1 t := by
  have h1e := hI.one
  have c : ∀ k < 4, ∀ l < 4, t.zlane (creg k) l = ctb s₀ (16 * (e + 0) - 16 + (4 * k + l)) := fun k hk l hl => by
    rw [hcp k hk l hl, hI.cp k hk l hl]; congr 1; omega_using []
  refine ⟨hE, fun _ k hk l hl => c k (by omega_using [hk]) l hl, fun _ k hk l hl => c (2 + k) (by omega_using [hk]) l hl, ?_⟩
  rw [ite_f (by omega_using [])]
  exact ⟨fun h => absurd h (by decide), fun _ _ => h2⟩

/-- `QL` after the last round: `Y` over the `e` groups, and the reduction
constant. -/
theorem QL.fin {ix : Bool} {s₀ : State} {T : Nat → Nat → Nat → Block} (hT : FinOk48 (hk s₀) T) {e : Nat}
    {s t : State} (hI : CInv ix s₀ T e s) (h : QL s₀ T e s 10 t) :
    CEnv s₀ T t ∧ t.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) ∧
      (∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0) ∧ ∀ l < 4, t.zlane .xmm1 l = poly := by
  obtain ⟨hE, _, _, h2⟩ := h
  rw [ite_t ⟨rfl, by decide⟩] at h2
  exact ⟨hE, by rw [h2.1]; exact yLast hT hI, h2.2.1, h2.2.2⟩

/-! ## No block after the last group -/

/-- The last group, in the copies, hashed, and the counter and `Y` stored. -/
theorem finalC_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : CInv ix s₀ T e s) :
    WP isa (.block (lastC ++ storeCtr ++ storeY)) s (Stitch.EPostM ix s₀) := by
  have hw := hp.wrap_w
  have h1e := hI.one
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hooks_run (gqLast (T := T) h1e s) 9 (Nat.le_refl _) s (hI.a.keys hp)
    (QL.start hI hI.env (fun _ _ _ _ => rfl) (fun _ _ => rfl))) fun s₁ ⟨hQ₁, f₁⟩ => ?_
  obtain ⟨_, y₁, _, _⟩ := QL.fin hT hI hQ₁
  have hm0₁ : s₁.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), f₁.zlane _ (by decide) 0 (by decide)]; exact hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm13 .xmm14 .rax s₁ hm0₁ (by rw [f₁.gpr, hI.rax, f₁.wr, hI.a.wr]; exact hp.c_in))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [f₁.gpr, hI.rax, f₁.mem] at m₂
  have hm0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), l₂ _ (by decide) 0 (by decide), State.zlane_lt2 _ _ (by decide)]
    exact hm0₁
  have gk : s₂.gpr = s.gpr := by rw [g₂, f₁.gpr]
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₂ hm0₂ (by
      rw [gk, wr₂, f₁.wr, hI.a.wr, hrcx]; exact hp.y_in)) fun s₃ ⟨m₃, g₃, rd₃, wr₃, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [gk, hrcx, m₂] at m₃
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.w_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.w_y.sub_left (Offset.sub_base _ (by omega_using [hk]))
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, by
      show s₃.rd = _; rw [rd₃, rd₂, f₁.rd, hI.a.rd], by
      show s₃.wr = _; rw [wr₃, wr₂, f₁.wr, hI.a.wr]⟩
  · show blockAt s₃.mem _ = _
    rw [m₃, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.out k (by omega_using [he, hk])
  · show blockAt s₃.mem (cp s₀) = _
    rw [m₃, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      f₁.zlane _ (by decide) 0 (by decide), hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show blockAt s₃.mem (yp s₀) = _
    rw [m₃, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), l₂ _ (by decide) 0 (by decide),
      y₁, he]
  · show Frame _ s₀.mem s₃.mem
    rw [m₃]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₃.gpr r = _
    rw [g₃, gk]; exact hI.gpr r h1 h2 h3 h4 h5

/-! ## The blocks after the last group, as a masked group -/

/-- `StitchZH.ksBatchG_ok`, for a last group in the copies: the `r` blocks
after it as a group of `k` registers, their counters made with the increment
loaded from the working space, and the copies hashed between the rounds
(`Q`). -/
theorem ksBatchC_ok {s₀ : State} (hnr : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14) {k r : Nat} (hk4 : k ≤ 4)
    (hr1 : 1 ≤ r) (hr15 : r ≤ 15) (hrk : r ≤ 4 * k) (hkr : 4 * k < r + 4)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (gqC true true 2 j)) s fun s' => Q (j + 1) s' ∧ ZFrame gRegs48 s s')
    (hq : ∀ j s s', Q j s → ZFrame gTmp s s' → Q j s')
    (pre : List Instr) (src : Reg) (hsrc : src ≠ .r10) (hs9 : src ≠ .r9) (hsa : src ≠ .rax)
    {A S W : Addr} {D T : Nat → Block} {y : Block} {c : Nat} {s : State}
    (hpre : ∀ t : State, t.gpr = s.gpr → WP isa (.block (.alu .add .rdx (.imm 256) :: pre)) t fun t' =>
      t'.gpr .rdx = A ∧ t'.gpr src = S ∧ (∀ q, q ≠ .rdx → q ≠ src → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hQ10 : ∀ t, Q 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧ ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0)
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (him : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (896 + 16 * l)) 128 = four)
    (hr11 : s.gpr .r11 = pp s₀) (hin : InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((896 : Nat) : Int)) 64)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hK : Keys (nr s₀) (sch s₀) s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) (hQ : Q 1 s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hW : s.gpr .rax = W)
    (hD : ∀ n < r, blockAt s.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (s.rd ++ s.wr) S (16 * r)) (hinD : InRegions s.wr A (16 * r))
    (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ksBatchC k pre src) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 =
        (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
          reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
        (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
          reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ l < 4, s'.zlane .xmm0 l = revMask := by
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  have hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  have hx11 : ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm11 := by decide
  have hGA : ∀ r ∈ gRegs48, r ∉ aregs := by decide
  have hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm11 := fun r hr => hx11 r (List.mem_of_mem_take hr)
  have h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega_using [hk4]
  -- The increment, and the counters.
  let q := s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)) 64 := by
    rw [hr11]; exact hin
  have hctrs : WP isa (.block (.vmovdqu32Load .xmm11 incAt :: Impl.Aes.X86_64.VaesZ.ctrsZ .xmm14 .xmm0 .xmm11
      (aregs.take k))) s fun s' =>
      (∀ i (h : i < (aregs.take k).length), ∀ l < 4,
        s'.zlane (aregs.take k)[i] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * i + l) (cb s₀)) revMask) ∧
      ZFrame (.xmm11 :: .xmm14 :: aregs.take k) s s' := by
    rw [WP.block_cons_iff]
    refine ⟨StitchZ.ldZ s .xmm11 q, by
      simp only [incAt, isa, exec, State.load512, Pclmul.ea_at, hin', ite_true, Option.map_some]; rfl, ?_⟩
    have f₀ : ZFrame [.xmm11] s (StitchZ.ldZ s .xmm11 q) :=
      ⟨rfl, rfl, rfl, rfl, fun r hr l hl => StitchZ.ldZ_zlane_ne _ _ (fun h => hr (by simp [h])) hl⟩
    refine WP.mono (VG.Proof.Aes.X86_64.VaesZ.ctrsZ_ok .xmm14 .xmm0 .xmm11 (by decide) (by decide) (aregs.take k) _
      (cb s₀) c hnd' hx'
      (fun l hl => by rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl]; exact hctr l hl)
      (fun l hl => by rw [StitchZ.ldZ_zlane_ne _ _ (by decide) hl]; exact hmsk l hl)
      (fun l hl => by rw [StitchZ.ldZ_zlane _ _ _ hl, StitchZ.ofInt_add_ofNat, hr11]; exact him l hl))
      fun s' ⟨e, _, f'⟩ => ⟨e, f₀.comp f'⟩
  refine WP.seq (WP.mono (WP.hkeep (by
      rw [List.all_cons, StitchZH.ctrsZ_keeps]; rfl) hctrs) fun s₁ ⟨⟨e₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have sub₁ : ∀ r ∈ (.xmm11 :: .xmm14 :: aregs.take k : List XReg), r ∈ gTmp := fun r hr => by
    simp only [List.mem_cons] at hr ⊢
    rcases hr with rfl | rfl | hr
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_take hr)))
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono sub₁)
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hnr (gqC true true 2)
    gRegs48 (fun r h hm => hGA r h (List.mem_of_mem_take hm)) Q
    (fun j hj h9 t hk hq' => WP.mono (WP.hkeep (gqC_keeps true true 2 j) (hg j hj h9 t hk.base hq'))
      fun _ ⟨⟨hq'', hf⟩, hh⟩ => ⟨hq'', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      simp only [List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_take hr))))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ n < r, XBinOp.eval .pshufb (s₂.zlane ((aregs.take k).getD (n / 4) .xmm0) (n % 4)) revMask =
      ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀)) := fun n hn => by
    have h : n / 4 < (aregs.take k).length := by rw [hlen]; omega_using [hrk, hn]
    rw [← List.getElem_eq_getD (h := h),
      (VG.Proof.Aes.X86_64.AesNi.aesWith_eq _ _ _ _ (by
        rw [e₂ _ (List.getElem_mem h) _ (by omega_using []), e₁ _ h _ (by omega_using [])])).symm,
      show c + 4 * (n / 4) + n % 4 = c + n by omega_using []]
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have hrd₂ : s₂.rd = s.rd := by rw [f₂.rd, f₁.rd]
  have hwr₂ : s₂.wr = s.wr := by rw [f₂.wr, f₁.wr]
  have m0₂ : ∀ l < 4, s₂.zlane .xmm0 l = revMask := fun l hl => by
    rw [f₂.zlane .xmm0 (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨by decide, fun h => absurd (List.mem_of_mem_take h) (by decide), by decide⟩) l hl,
      f₁.zlane .xmm0 (by
        simp only [List.mem_cons, not_or]
        exact ⟨by decide, by decide, fun h => absurd (List.mem_of_mem_take h) (by decide)⟩) l hl]
    exact hmsk l hl
  obtain ⟨q1, q2⟩ := hQ10 s₂ hQ₂
  refine WP.seq (WP.mono (hpre s₂ hg₂) fun s₃ ⟨d₃, src₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  have gk₃ : ∀ q, q ≠ .rdx → q ≠ src → s₃.gpr q = s.gpr q := fun q h1 h2 => by rw [g₃ q h1 h2, hg₂]
  refine WP.mono (StitchZH.tailG_ok src hsrc hk4 hr1 hr15 hrk hkr (t := s₃)
      (K := fun n => ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) (D := D) (T := T) (y := y)
      (by rw [gk₃ _ (by decide) (Ne.symm hs9), h9]) d₃ src₃ (by rw [gk₃ _ (by decide) (Ne.symm hsa), hW])
      (fun n hn => by rw [l₃]; exact ks n hn)
      (fun n hn => by rw [m₃, hm₂]; exact hD n hn) (fun n hn => by rw [m₃, hm₂]; exact hT n hn)
      (by rw [rd₃, wr₃, hrd₂, hwr₂]; exact hinS) (by rw [wr₃, hwr₂]; exact hinD)
      (by rw [rd₃, wr₃, hrd₂, hwr₂]; exact hinW) hsep hWA
      (fun l hl => by rw [l₃]; exact m0₂ l hl)
      (fun l hl => by rw [l₃]; exact q1 l hl) (fun l hl => by rw [l₃]; exact q2 l hl))
    fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨b', by rw [← hm₂, ← m₃]; exact f', y', y1',
      fun q h1 h2 h3 => by rw [g' q h1, gk₃ q h2 h3], by rw [rd', rd₃, hrd₂], by rw [wr', wr₃, hwr₂],
      fun l hl => by rw [z' .xmm0 (by decide) (by decide) l hl, l₃]; exact m0₂ l hl⟩

/-- `ksBatchC` of `⌈r / 4⌉` registers, from `r10 = 16 r` (`StitchZH.ksSelG_ok`). -/
theorem ksSelC_ok {s₀ : State} (hnr : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14) {r : Nat} (hr1 : 1 ≤ r) (hr15 : r ≤ 15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (gqC true true 2 j)) s fun s' => Q (j + 1) s' ∧ ZFrame gRegs48 s s')
    (hq : ∀ j s s', Q j s → ZFrame gTmp s s' → Q j s')
    (pre : List Instr) (src : Reg) (hsrc : src ≠ .r10) (hs9 : src ≠ .r9) (hsa : src ≠ .rax)
    {A S W : Addr} {D T : Nat → Block} {y : Block} {c : Nat} {s : State}
    (hpre : ∀ t : State, t.gpr = s.gpr → WP isa (.block (.alu .add .rdx (.imm 256) :: pre)) t fun t' =>
      t'.gpr .rdx = A ∧ t'.gpr src = S ∧ (∀ q, q ≠ .rdx → q ≠ src → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hQ10 : ∀ t, Q 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧ ∀ l < 4, t.zlane .xmm2 l = if l = 0 then y else 0)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask)
    (him : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (896 + 16 * l)) 128 = four)
    (hr11 : s.gpr .r11 = pp s₀) (hin : InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((896 : Nat) : Int)) 64)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hK : Keys (nr s₀) (sch s₀) s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) (hQ : Q 1 s)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (hW : s.gpr .rax = W)
    (hD : ∀ n < r, blockAt s.mem (S + BitVec.ofNat 64 (16 * n)) = D n)
    (hT : ∀ n < r, s.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128 = T n)
    (hinS : InRegions (s.rd ++ s.wr) S (16 * r)) (hinD : InRegions s.wr A (16 * r))
    (hinW : InRegions (s.rd ++ s.wr) W (16 * r))
    (hsep : ∀ n q', q' < n / 4 → n < r →
      Region.Disjoint ⟨S + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A + BitVec.ofNat 64 (64 * q'), 64⟩)
    (hWA : ∀ n < r, Region.Disjoint ⟨W + BitVec.ofNat 64 (16 * n), 16⟩ ⟨A, 16 * r⟩) :
    WP isa (Impl.Gcm.X86_64.StitchZH.ksSelC pre src) s fun s' =>
      (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
        D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
      Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
      s'.zlane .xmm2 0 =
        (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
          reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
        (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
          reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ l < 4, s'.zlane .xmm0 l = revMask := by
  -- A batch of `k` registers, from a state the comparisons leave as `s` was.
  have br : ∀ k, r ≤ 4 * k → 4 * k < r + 4 → k ≤ 4 → ∀ t : State, t.gpr = s.gpr →
      (∀ x l, t.zlane x l = s.zlane x l) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → HKeep s t →
      WP isa (Impl.Gcm.X86_64.StitchZH.ksBatchC k pre src) t fun s' =>
        (∀ n < r, blockAt s'.mem (A + BitVec.ofNat 64 (16 * n)) =
          D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) ∧
        Frame [⟨A, 16 * r⟩] s.mem s'.mem ∧
        s'.zlane .xmm2 0 =
          (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 0 r) ^^^
            reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 2 r)) ^^^
          (reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 1 r) ^^^
            reduceB (StitchZH.laneAccG (fun n => D n ^^^ ciph s₀ (Nat.repeat inc32 (c + n) (cb s₀))) T y 3 r)) ∧
        (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
        (∀ q, q ≠ .r10 → q ≠ .rdx → q ≠ src → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        ∀ l < 4, s'.zlane .xmm0 l = revMask := by
    intro k hrk hkr hk4 t hg' hl hm hrd' hwr' hh
    have ft : ZFrame gTmp s t := ⟨hg', hm, hrd', hwr', fun x _ l _ => hl x l⟩
    have hKt : Keys (nr s₀) (sch s₀) t := ZFrame.of_keys hK ft
    refine WP.mono (ksBatchC_ok hnr hk4 hr1 hr15 hrk hkr Q hg hq pre src hsrc hs9 hsa
      (A := A) (S := S) (W := W) (D := D) (T := T) (c := c)
      (fun t' h => hpre t' (h.trans hg')) hQ10
      (fun l hl' => by rw [hl]; exact hctr l hl') (fun l hl' => by rw [hl]; exact hmsk l hl')
      (fun l hl' => by rw [hm]; exact him l hl') (by rw [hg']; exact hr11) (by rw [hrd', hwr']; exact hin)
      (by rw [hg']; exact hrsi) hKt (hCache.keep hh hKt) (hq 1 s t hQ ft)
      (by rw [hg']; exact h9) (by rw [hg']; exact hW) (fun n hn => by rw [hm]; exact hD n hn)
      (fun n hn => by rw [hm]; exact hT n hn) (by rw [hrd', hwr']; exact hinS) (by rw [hwr']; exact hinD)
      (by rw [hrd', hwr']; exact hinW) hsep hWA)
      fun s' ⟨b', f', y', y1', g', rd', wr', z'⟩ => ⟨b', by rw [← hm]; exact f', y', y1',
        fun q h1 h2 h3 => by rw [g' q h1 h2 h3, hg'], by rw [rd', hrd'], by rw [wr', hwr'], z'⟩
  have c65 : BitVec.signExtend 64 (65 : BitVec 32) = BitVec.ofNat 64 65 := by decide
  have c129 : BitVec.signExtend 64 (129 : BitVec 32) = BitVec.ofNat 64 129 := by decide
  have c193 : BitVec.signExtend 64 (193 : BitVec 32) = BitVec.ofNat 64 193 := by decide
  have t16 : (s.gpr .r10).toNat = 16 * r := by
    rw [h10, toNat_ofNat_lt (by omega_using [hr15])]
  unfold Impl.Gcm.X86_64.StitchZH.ksSelC
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZH.cmp10_ok s 65 65 c65))
    fun s₁ ⟨⟨cf₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  rw [t16, show (BitVec.ofNat 64 65).toNat = 65 from rfl] at cf₁
  refine WP.ite (decide (16 * r < 65)) (by simp only [eval, cf₁]) (fun h => ?_) (fun h => ?_)
  · exact br 1 (by simp at h; omega_using [h]) (by omega_using [hr1]) (by decide) s₁ g₁ l₁ m₁ rd₁ wr₁ hh₁
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZH.cmp10_ok s₁ 129 129 c129))
    fun s₂ ⟨⟨cf₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
  rw [g₁, t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at cf₂
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, cf₂]) (fun h' => ?_) (fun h' => ?_)
  · exact br 2 (by simp at h'; omega_using [h']) (by simp at h; omega_using [h]) (by decide) s₂ (by rw [g₂, g₁])
      (fun x l => by rw [l₂, l₁]) (by rw [m₂, m₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (hh₁.trans hh₂)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZH.cmp10_ok s₂ 193 193 c193))
    fun s₃ ⟨⟨cf₃, g₃, l₃, m₃, rd₃, wr₃⟩, hh₃⟩ => ?_)
  rw [g₂, g₁, t16, show (BitVec.ofNat 64 193).toNat = 193 from rfl] at cf₃
  refine WP.ite (decide (16 * r < 193)) (by simp only [eval, cf₃]) (fun h'' => ?_) (fun h'' => ?_)
  · exact br 3 (by simp at h''; omega_using [h'']) (by simp at h'; omega_using [h']) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)
  · exact br 4 (by omega_using [hr15]) (by simp at h''; omega_using [h'']) (by decide) s₃ (by rw [g₃, g₂, g₁])
      (fun x l => by rw [l₃, l₂, l₁]) (by rw [m₃, m₂, m₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
      ((hh₁.trans hh₂).trans hh₃)

/-- The key schedule, in a memory where only the output, the working space
and the counter were written. -/
theorem sch_frameC {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hck : (cR s₀).Disjoint (Stitch.kR s₀))
    {m : Mem} (hf : Frame [Stitch.wR ix s₀, pR s₀, cR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_using [hn]) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.w_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)
  · exact hck.symm.sub_left (Region.sub_prefix hn)

/-- `StitchZH.remG_ok`, for a last group in the copies, in place or out of
place: the counter after all the blocks stored, the `r` blocks after the
last group encrypted as a masked group while the copies are hashed, and `Y`
stored. `pre` points `src` at the `r` blocks once `rdx` is advanced. -/
theorem remCore_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hck : (cR s₀).Disjoint (Stitch.kR s₀))
    (hdc : (Stitch.dR s₀).Disjoint (cR s₀))
    {P : Nat → Nat → Block} (hr : StitchZH.RemOkG (hk s₀) P) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) {e : Nat} {s : State} (hI : CInv ix s₀ T e s)
    (hex : nb s₀ - 16 * (e - 1) < 32) (hne : nb s₀ ≠ 16 * e)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (pre : List Instr) (src : Reg) (hsrc : src ≠ .r10) (hs9 : src ≠ .r9) (hsa : src ≠ .rax)
    (hsq : ∀ q, q ≠ .rdx → (ix = true → q ≠ .r8) → q ≠ src)
    (hpre : ∀ t : State, t.gpr .rdx = s.gpr .rdx → (ix = true → t.gpr .r8 = s.gpr .r8) →
      WP isa (.block (.alu .add .rdx (.imm 256) :: pre)) t fun t' =>
        t'.gpr .rdx = Stitch.wAddr ix s₀ (16 * e) ∧ t'.gpr src = bAddr s₀ (16 * e) ∧
        (∀ q, q ≠ .rdx → q ≠ src → t'.gpr q = t.gpr q) ∧
        (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchZH.remSetup)
      (.seq (Impl.Gcm.X86_64.StitchZH.ksSelC pre src) (.block storeY))) s (Stitch.EPostM ix s₀) := by
  have hw := hp.wrap_w
  have hwd := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  -- The `r` blocks after the `16 e` encrypted.
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega_using [hne, hle, hr_def]
  have hr15 : r ≤ 15 := by omega_using [hex, h1e, hr_def]
  have hnb : nb s₀ = 16 * e + r := by omega_using [hle, hr_def]
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9]; congr 1; omega_using [h1e, hle, hr_def]
  have hrax : s.gpr .rax = cp s₀ := hI.rax
  have hr11 : s.gpr .r11 = pp s₀ := hI.a.r11
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZH.remSetup_ok s hr1 hr15 hr9
    (by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide))
    (by rw [hrax, hI.a.wr]; exact in_sub_int hp.c_in (by omega_using []))))
    fun s₁ ⟨⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hrax, e0] at m₁
  rw [hr11] at ax₁
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have gk₁ : ∀ q, q ≠ .r10 → q ≠ .rax → s₁.gpr q = s.gpr q := g₁
  -- What the counter's store keeps of the memory before it.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) → blockAt s₁.mem p = blockAt s.mem p := fun p hc => by
    rw [m₁, show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have toP : ∀ o : Nat, o + 16 ≤ 1024 →
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho => by
    rw [m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_using [ho]))).sep
      (Region.contains_self _ _) cw) (by decide)]
  have hE₁ : CEnv s₀ T s₁ := ⟨by rw [gk₁ _ (by decide) (by decide)]; exact hr11,
    fun g hg k hk l hl => by rw [toP _ (by simp only [tab]; omega_using [hk, hl])]; exact hI.env.pv g hg k hk l hl,
    fun l hl => by rw [toP _ (by omega_using [hl])]; exact hI.env.pm l hl,
    fun o ho => by rw [rd₁, wr₁]; exact hI.env.inp o ho⟩
  have hF₁ : Frame [Stitch.wR ix s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ cw
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁, hI.a.rd]
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁, hI.a.wr]
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ :=
    ⟨by rw [gk₁ _ (by decide) (by decide), hI.a.rdi, sch_frameC hp hck hF₁],
      by rcases hp.rounds with h | h | h <;> omega_using [h],
      fun j hj => by rw [rd₁, wr₁, gk₁ _ (by decide) (by decide)]; exact (hI.a.keys hp).keys j hj⟩
  have hCache₁ := hCache.keep hh₁ hK₁
  -- The copies, hashed while the `r` blocks are encrypted.
  have cne : ∀ k < 4, creg k ≠ .xmm13 := by decide
  have hQ₁ : QL s₀ T e s 1 s₁ :=
    QL.start hI hE₁ (fun k hk l hl => z₁ _ (cne k hk) l hl) (fun l hl => z₁ _ (by decide) l hl)
  have hQ10 : ∀ t, QL s₀ T e s 10 t → (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      ∀ l < 4, t.zlane .xmm2 l =
        if l = 0 then ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) else 0 := fun t h => by
    obtain ⟨_, y0, y1, p1⟩ := QL.fin hT hI h
    refine ⟨p1, fun l hl => ?_⟩
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact y0
    · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega_using [hl0]))]; exact y1 l hl0 hl
  -- Where the `r` blocks, the data they are made from, and their powers are.
  let A := Stitch.wAddr ix s₀ (16 * e)
  let S := bAddr s₀ (16 * e)
  let W := pp s₀ + BitVec.ofNat 64 (256 - 16 * r)
  have eA : ∀ j, A + BitVec.ofNat 64 (16 * j) = Stitch.wAddr ix s₀ (16 * e + j) := fun j => by
    show Stitch.wp ix s₀ + _ + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  have eS : ∀ j, S + BitVec.ofNat 64 (16 * j) = bAddr s₀ (16 * e + j) := fun j => by
    show dp s₀ + _ + _ = _
    rw [Offset.add_add, ← Nat.mul_add]
  refine WP.seq (WP.mono (ksSelC_ok hp.rounds hr1 hr15 (QL s₀ T e s) (gqLast h1e s)
    (fun j t t' h f => h.zframe f (by decide)) pre src hsrc hs9 hsa
    (A := A) (S := S) (W := W) (D := fun n => blockAt s₁.mem (S + BitVec.ofNat 64 (16 * n)))
    (T := fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128) (c := 16 * e)
    (fun t ht => hpre t (by rw [ht, gk₁ _ (by decide) (by decide)])
      (fun _ => by rw [ht, gk₁ _ (by decide) (by decide)]))
    hQ10 a10₁ (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [z₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [toP _ (by omega_using [hl])]; exact hI.a.im l hl)
    (by rw [gk₁ _ (by decide) (by decide)]; exact hr11)
    (by rw [rd₁, wr₁]; exact hI.env.inp 896 (by decide))
    (by rw [gk₁ _ (by decide) (by decide)]; exact hI.a.rsi) hK₁ hCache₁ hQ₁
    (by rw [gk₁ _ (by decide) (by decide)]; exact hr9) ax₁ (fun _ _ => rfl) (fun _ _ => rfl)
    (by rw [hrd₁, hwr₁]; exact in_sub hp.d_in (by omega_using [hle, hr_def]))
    (by rw [hwr₁]; exact in_sub hp.w_in (by omega_using [hle, hr_def]))
    (by rw [hrd₁, hwr₁]; exact in_rdwr (in_sub hp.p_in (by omega_using [hr15])))
    (fun n q' hq hn' => by
      show Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 (16 * (16 * e)) + BitVec.ofNat 64 (16 * n), 16⟩
        ⟨Stitch.wp ix s₀ + BitVec.ofNat 64 (16 * (16 * e)) + BitVec.ofNat 64 (64 * q'), 64⟩
      rw [Offset.add_add, Offset.add_add]
      cases ix
      · exact Offset.disjoint _ (.inr (by omega_using [hq])) (by omega_using [hex, hne, hwd, h1e, hle, hn, hr_def, hr1, hr15, hnb, hq, hn', hw]) (by omega_using [hwd, hnb, hq, hn'])
      · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega_using [hnb, hn']))).sub_right (Offset.sub_base _ (by omega_using [hex, hne, hwd, h1e, hle, hn, hr_def, hr1, hr15, hnb, hq, hn', hw])))
    (fun n hn' => by
      show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * n), 16⟩
        ⟨Stitch.wp ix s₀ + BitVec.ofNat 64 (16 * (16 * e)), 16 * r⟩
      rw [Offset.add_add]
      exact (hp.w_p.symm.sub_left (Offset.sub_base _ (by omega_using [hr15, hn']))).sub_right (Offset.sub_base _ (by omega_using [hle, hr_def]))))
    fun s₂ ⟨b₂, f₂, y₂, _, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- `Y` stored.
  have hrcx : s₂.gpr .rcx = yp s₀ := by
    rw [g₂ _ (by decide) (by decide) (hsq _ (by decide) (fun _ => by decide)), gk₁ _ (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide) (by decide)
  have m0₂ : s₂.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide)]; exact z₂ 0 (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16Z_ok .xmm2 .xmm2 .rcx s₂ m0₂ (by rw [hrcx, wr₂, hwr₁]; exact hp.y_in))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx] at m₆
  have cW : ∀ k, k < nb s₀ → Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.w_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have cD : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hdc.sub_left (Offset.sub_base _ (by omega_using [hk]))
  have yW : ∀ k, k < nb s₀ → Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.w_y.sub_left (Offset.sub_base _ (by omega_using [hk]))
  -- The `r` blocks, encrypted.
  have hX : ∀ j < r, blockAt s₁.mem (S + BitVec.ofNat 64 (16 * j)) ^^^
      ciph s₀ (Nat.repeat inc32 (16 * e + j) (cb s₀)) = ctb s₀ (16 * e + j) := fun j hj => by
    have hk : 16 * e + j < nb s₀ := by omega_using [hnb, hj]
    rw [eS, toS _ (cD _ hk), hI.a.src _ hk (by omega_using [])]
  -- The blocks.
  have hb₂ : ∀ k < nb s₀, blockAt s₂.mem (Stitch.wAddr ix s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame f₂ (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_using [hke])) (by omega_using [hw, hk]) (by omega_using [hex, hne, hw, hwd, h1e, hle, hn, hr_def, hr1, hr15, hnb, hk, hke])),
        toS _ (cW k hk), hI.a.out k hke]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_using [hke]⟩
      have hj : j < r := by omega_using [hr_def, hk]
      rw [← eA, b₂ j hj, hX j hj]
  have hTt : ∀ j < r, s₁.mem.readW (W + BitVec.ofNat 64 (16 * j)) 128 = P ((16 - r + j) / 4) ((16 - r + j) % 4) :=
    fun j hj => by
      have hm : 16 - r + j < 16 := by omega_using [hr15, hj]
      show s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 128 = _
      rw [Offset.add_add,
        show 256 - 16 * r + 16 * j = tab 2 + 64 * ((16 - r + j) / 4) + 16 * ((16 - r + j) % 4) by
          simp only [tab]; omega_using [],
        toP _ (by simp only [tab]; omega_using [hr15, hj]), hI.env.pv 2 (by decide) _ (by omega_using [hr15, hj]) _ (by omega_using []), hT2]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₆.mem _ = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yW k hk) rfl, hb₂ k hk]
  · show blockAt s₆.mem (cp s₀) = _
    rw [m₆, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl,
      VG.Proof.Aes.X86_64.AesNi.blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.w_c.symm.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hle, hr_def]))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), hI.a.ctr 0 (by decide),
      Nat.add_zero, VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₆.mem (yp s₀) = _
    have cg : ∀ l, StitchZH.laneAccG (fun n => blockAt s₁.mem (S + BitVec.ofNat 64 (16 * n)) ^^^
        ciph s₀ (Nat.repeat inc32 (16 * e + n) (cb s₀))) (fun n => s₁.mem.readW (W + BitVec.ofNat 64 (16 * n)) 128)
        (ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀))) l r =
        StitchZH.laneAccG (fun j => ctb s₀ (16 * e + j)) (fun j => P ((16 - r + j) / 4) ((16 - r + j) % 4))
          (ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀))) l r :=
      fun l => StitchZH.laneAccG_congr _ l r hX hTt
    rw [m₆, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), y₂, cg 0, cg 1,
      cg 2, cg 3, hr r hr1 hr15, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₆.mem
    have F1 : Frame [cR s₀, yR s₀, Stitch.wR ix s₀, pR s₀] s₀.mem s₁.mem :=
      hF₁.mono fun r hr => by simp at hr ⊢; rcases hr with h | h | h <;> simp [h]
    have F2 : Frame [cR s₀, yR s₀, Stitch.wR ix s₀, pR s₀] s₁.mem s₂.mem := f₂.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨Stitch.wR ix s₀, by simp,
        Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_using [hle, hr_def])⟩
    rw [m₆]
    exact (F1.trans F2).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4 h5
    show s₆.gpr q = _
    rw [g₆, g₂ q h5 h2 (hsq q h2 h3), gk₁ q h5 h1]
    exact hI.gpr q h1 h2 h3 h4 h5
  · show s₆.rd = _
    rw [rd₆, rd₂]; exact hrd₁
  · show s₆.wr = _
    rw [wr₆, wr₂]; exact hwr₁

/-- `remC`, in place or out of place. -/
theorem remC_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hck : (cR s₀).Disjoint (Stitch.kR s₀))
    (hdc : (Stitch.dR s₀).Disjoint (cR s₀))
    {P : Nat → Nat → Block} (hr : StitchZH.RemOkG (hk s₀) P) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) {e : Nat} {s : State} (hI : CInv ix s₀ T e s)
    (hex : nb s₀ - 16 * (e - 1) < 32) (hne : nb s₀ ≠ 16 * e)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (Impl.Gcm.X86_64.StitchZH.remC ix) s (Stitch.EPostM ix s₀) := by
  have hw := hp.wrap_w
  have h1e := hI.one
  have hle := hI.a.le
  have ha := hI.rdx
  have hA : s.gpr .rdx + 256 = Stitch.wAddr ix s₀ (16 * e) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (show (s.gpr .rdx).toNat + 256 < 2 ^ 64 by omega_using [hne, hw, h1e, hle, ha]), BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (16 * e) < 2 ^ 64 by omega_using [hne, hw, hle]), Nat.mod_eq_of_lt (by omega_using [hne, hw, hle])]
    omega_using [h1e, ha]
  cases ix
  · refine remCore_ok hp hck hdc hr hT hT2 hI hex hne hCache [] .rdx (by decide) (by decide) (by decide)
      (fun q h _ => h) (fun t ht _ => ?_)
    exact WP.mono (StitchZH.addRdx_ok t) fun t' ⟨d', g', l', m', rd', wr'⟩ =>
      ⟨by rw [d', ht]; exact hA, by rw [d', ht]; exact hA, fun q h _ => g' q h, l', m', rd', wr'⟩
  · refine remCore_ok hp hck hdc hr hT hT2 hI hex hne hCache [.alu .add .r8 (.reg .rdx)] .r8 (by decide)
      (by decide) (by decide) (fun q _ h => h rfl) (fun t ht ht8 => ?_)
    refine WP.mono (StitchZHTo.addRdxR8_ok t) fun t' ⟨d', r8', g', l', m', rd', wr'⟩ =>
      ⟨by rw [d', ht]; exact hA, ?_, g', l', m', rd', wr'⟩
    rw [r8', ht8 rfl, ht, hI.r8 rfl, hA]
    show dp s₀ - Stitch.op s₀ + (Stitch.op s₀ + BitVec.ofNat 64 (16 * (16 * e))) =
      dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The end of `midRest`: the last group, in the copies, and the blocks
after it if any. -/
theorem tailC_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hck : (cR s₀).Disjoint (Stitch.kR s₀))
    (hdc : (Stitch.dR s₀).Disjoint (cR s₀))
    {P : Nat → Nat → Block} (hr : StitchZH.RemOkG (hk s₀) P) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) {e : Nat} {s : State} (hI : CInv ix s₀ T e s)
    (hex : nb s₀ - 16 * (e - 1) < 32)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) :
    WP isa (Impl.Gcm.X86_64.StitchZH.tailC ix) s (Stitch.EPostM ix s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1e := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (WP.hkeep (by decide) (StitchZH.cmp16_ok s)) fun s₁ ⟨⟨zf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₁ := hI.of_eq g l m rd wr
  have hz : (s.gpr .r9 - 16 == 0) = decide (nb s₀ = 16 * e) := by
    rw [hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_sub_ofNat (by omega_using [h1e, hle]) (by omega_using [hex])]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * (e - 1) - 16 = 0 by omega_using [h], decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * (e - 1) - 16) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hex])] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_using [h1e, hle, h, this, h0]
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, zf, hz]) (fun h => ?_) (fun h => ?_)
  · exact finalC_ok hp hT (by simpa using h) hI₁
  · exact remC_ok hp hck hdc hr hT hT2 hI₁ hex (by simpa using h) (hCache.keep hh (hI₁.a.keys hp))

/-! ## The first group -/

/-- The increment kept in the working space (`CA`), after the powers of 48
blocks and the reduction constant are stored there (`CEnv`). -/
theorem storeInc_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) {T : Nat → Nat → Nat → Block} {c : Nat}
    {s : State} (hA : AInvM ix s₀ c s) (hr11 : s.gpr .r11 = pp s₀)
    (hv : ∀ g < 3, ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm : ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) :
    WP isa (.block [.vmovdqu32Store incAt .xmm15]) s fun s' =>
      CA ix s₀ c s' ∧ CEnv s₀ T s' ∧ s'.gpr = s.gpr ∧ ∀ r l, s'.zlane r l = s.zlane r l := by
  have hw := hp.wrap_w
  have hwd := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hA.le
  have e896 : s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int) = pp s₀ + BitVec.ofNat 64 896 := by
    rw [hr11, BitVec.ofInt_natCast]
  have hin896 : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((896 : Nat) : Int)) 64 := by
    rw [hA.wr, e896]; exact in_sub hp.p_in (by decide)
  let s₁ := s.setMem (s.mem.writeW (pp s₀ + BitVec.ofNat 64 896) (s.zmm .xmm15))
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [incAt, isa, exec, State.store512_eq, Pclmul.ea_at, hin896, ite_true]; rw [e896],
    WP.block_nil ?_⟩
  have ms : s₁.mem = s.mem.writeW (pp s₀ + BitVec.ofNat 64 896) (s.zmm .xmm15) := rfl
  have F₁ : Frame [⟨pp s₀ + BitVec.ofNat 64 896, 64⟩] s.mem s₁.mem :=
    (Frame.refl _ s.mem).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have kpw : ∀ o, o + 16 ≤ 896 →
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho =>
    Mem.readW_writeW_sep (Offset.sep (pp s₀) (d := o) (n := 128 / 8) (e := 896) (k := 512 / 8) (by omega_using [ho]) (by omega_using [ho])
      (by omega_using [])) (by decide)
  have sepW : ∀ k < nb s₀, ∀ r ∈ [(⟨pp s₀ + BitVec.ofNat 64 896, 64⟩ : Region)],
      Region.Disjoint ⟨Stitch.wAddr ix s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.w_p.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Offset.sub_base _ (by decide))
  have sepD : ∀ k < nb s₀, ∀ r ∈ [(⟨pp s₀ + BitVec.ofNat 64 896, 64⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.d_p.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Offset.sub_base _ (by decide))
  refine ⟨⟨hle, hA.ctr, hA.msk, fun l hl => ?_, hr11, hA.rdi, hA.rsi, hA.r10, ?_,
    fun k hk => by
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame F₁ (sepW k (by omega_using [hle, hk]))]; exact hA.out k hk,
    fun k hk hc => by
      rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame F₁ (sepD k hk)]; exact hA.src k hk hc,
    hA.rd, hA.wr⟩,
    ⟨hr11, fun g hg k hk l hl => by rw [kpw _ (by simp only [tab]; omega_using [hk, hl])]; exact hv g hg k hk l hl,
      fun l hl => by rw [kpw _ (by omega_using [hl])]; exact hm l hl,
      fun o ho => by
        show InRegions (s.rd ++ s.wr) _ 64
        rw [hA.rd, hA.wr]; exact in_rdwr (in_sub_int hp.p_in ho)⟩,
    rfl, fun _ _ => rfl⟩
  · rw [ms, show pp s₀ + BitVec.ofNat 64 (896 + 16 * l) = pp s₀ + BitVec.ofNat 64 896 + BitVec.ofNat 64 (16 * l) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    rw [StitchZ.readW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl]
    exact hA.inc l hl
  · rw [ms]
    exact hA.frame.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _
      (Offset.contains_base _ (by decide) (by decide))

/-! ## A message of 48 to 143 blocks -/

/-- `StitchZH.midRest`, after the setup (`s`) and the powers of 48 blocks
(`s₁`): the whole message, in place or out of place. -/
theorem midRestM_ok {ix : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hck : (cR s₀).Disjoint (Stitch.kR s₀))
    (hdc : (Stitch.dR s₀).Disjoint (cR s₀))
    {P : Nat → Nat → Block} (hr : StitchZH.RemOkG (hk s₀) P) {T : Nat → Nat → Nat → Block}
    (hT : FinOk48 (hk s₀) T) (hT2 : ∀ k l, T 2 k l = P k l) (h16 : 16 ≤ nb s₀)
    {s s₁ : State} (hR : ReadyM ix s₀ P s) (hA₁ : AInvM ix s₀ 0 s₁)
    (hv₁ : ∀ g < 3, ∀ k < 4, ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l)
    (hm₁ : ∀ l < 4, s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (832 + 16 * l)) 128 = poly) (hg₁ : s₁.gpr = s.gpr)
    (hl₁ : ∀ l < 4, s₁.zlane .xmm2 l = s.zlane .xmm2 l)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s₁) :
    WP isa (Impl.Gcm.X86_64.StitchZH.midRest ix) s₁ (Stitch.EPostM ix s₀) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hr11 : s.gpr .r11 = pp s₀ := hR.gpr .r11 (by decide) (by decide) (fun _ => by decide) (by decide)
  unfold Impl.Gcm.X86_64.StitchZH.midRest
  -- The increment kept.
  refine WP.seq (WP.mono (WP.hkeep (by decide) (storeInc_ok hp (T := T) hA₁ (by rw [hg₁]; exact hr11) hv₁ hm₁))
    fun s₂ ⟨⟨hA₂, hE₂, g₂, l₂⟩, hh₂⟩ => ?_)
  have gs₂ : s₂.gpr = s.gpr := g₂.trans hg₁
  have hK₂ := hCache.keep hh₂ (hA₂.keys hp)
  -- The first group, with nothing between its rounds.
  let Q : Nat → State → Prop := fun _ t => CEnv s₀ T t ∧ ∀ l < 4, t.zlane .xmm2 l = s.zlane .xmm2 l
  refine WP.seq (WP.mono (grpM_ok hp (fun _ => []) [] (by simp) Q (Q 0)
      (fun _ _ _ t _ hq => WP.block_nil ⟨hq, ZFrame.refl _ _⟩)
      (fun _ t t' h f => ⟨h.1.zframe f, fun l hl => by rw [f.zlane _ (by decide) l hl]; exact h.2 l hl⟩)
      (c := 0) (j := 0) ?_ (by omega_using [h16]) hA₂ hK₂ (fun _ => rfl) (fun hi => by rw [gs₂]; exact hR.r8 hi)
      (by rw [gs₂, hR.rdx]) ⟨hE₂, fun l hl => by rw [l₂, hl₁ l hl]⟩)
    fun s₃ ⟨hA₃, ⟨hE₃, y₃⟩, g₃, cp₃, hK₃⟩ => ?_)
  · -- The output written and the copies made keep the working space and `Y`.
    rintro t t' ⟨hE', h2⟩ hgpr hrd hwr hl hf
    exact ⟨⟨by rw [hgpr]; exact hE'.r11,
      fun g' hg' k hk l hl' => by
        rw [StitchZ.keepWM hp (c := 0) (by omega_using [h16]) hf (by simp only [tab]; omega_using [hk, hl'])]; exact hE'.pv g' hg' k hk l hl',
      fun l hl' => by rw [StitchZ.keepWM hp (c := 0) (by omega_using [h16]) hf (by omega_using [hl'])]; exact hE'.pm l hl',
      fun o ho => by rw [hrd, hwr]; exact hE'.inp o ho⟩,
      fun l hl' => by rw [hl .xmm2 (by decide) (by decide) (by decide) l hl']; exact h2 l hl'⟩
  have gs₃ : s₃.gpr = s.gpr := g₃.trans gs₂
  have hC₃ : CInv ix s₀ T 1 s₃ :=
    ⟨by simpa using hA₃, Nat.le_refl _, by rw [gs₃, hR.rdx]; simp,
      by rw [gs₃, hR.gpr _ (by decide) (by decide) (fun _ => by decide) (by decide)]; simp,
      by rw [gs₃]; exact hR.rax, fun hi => by rw [gs₃]; exact hR.r8 hi,
      fun r h1 h2 h3 _ h5 => by rw [gs₃]; exact hR.gpr r h1 h2 h3 h5, hE₃,
      fun k hk l hl => by rw [cp₃ k hk l hl],
      by rw [y₃ 0 (by decide), hR.y]; simp [ghashFrom],
      fun l h1 h4 => by rw [y₃ l h4]; exact hR.y1 l h1 h4⟩
  -- The groups after it, and the end.
  refine WP.seq (WP.mono (loopsC_ok hp hT hC₃ hK₃) fun s₄ ⟨e, hex, hC₄, hK₄⟩ => ?_)
  exact tailC_ok hp hck hdc hr hT hT2 hC₄ hex hK₄

/-! ## Which messages -/

/-- `sub r9, i`. -/
theorem subR9_ok (t : State) (i : BitVec 32) (v : BitVec 64) (hi : BitVec.signExtend 64 i = v) :
    WP isa (.block [.alu .sub .r9 (.imm i)]) t fun t' =>
      t'.gpr .r9 = t.gpr .r9 - v ∧ (∀ q, q ≠ .r9 → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, hi, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `add r9, i`. -/
theorem addR9_ok (t : State) (i : BitVec 32) (v : BitVec 64) (hi : BitVec.signExtend 64 i = v) :
    WP isa (.block [.alu .add .r9 (.imm i)]) t fun t' =>
      t'.gpr .r9 = t.gpr .r9 + v ∧ (∀ q, q ≠ .r9 → t'.gpr q = t.gpr q) ∧
      (∀ x l, t'.zlane x l = t.zlane x l) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, hi, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `midTest` and `midUndo`: `a` runs for 48 to 143 blocks and `b` for the
other numbers, each from a state that differs from `s` in its flags only. -/
theorem midSel_ok {Q : State → Prop} {a b : Prog isa} (s : State)
    (ha : 48 ≤ (s.gpr .r9).toNat → (s.gpr .r9).toNat < 144 → ∀ t, ZFrame [] s t → HKeep s t → WP isa a t Q)
    (hb : ¬ (48 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < 144) → ∀ t, ZFrame [] s t → HKeep s t → WP isa b t Q) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchZH.midTest)
      (.ite .b (.seq (.block Impl.Gcm.X86_64.StitchZH.midUndo) a)
        (.seq (.block Impl.Gcm.X86_64.StitchZH.midUndo) b))) s Q := by
  have hlt := (s.gpr .r9).isLt
  have e48 : BitVec.signExtend 64 Impl.Gcm.X86_64.StitchZC.bigMinC = 48 := by decide
  have e96 : BitVec.signExtend 64 (Impl.Gcm.X86_64.StitchZ.bigMinPE - Impl.Gcm.X86_64.StitchZC.bigMinC) =
      BitVec.ofNat 64 96 := by decide
  have ht : WP isa (.block Impl.Gcm.X86_64.StitchZH.midTest) s fun s' =>
      s'.cf = some (decide (48 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < 144)) ∧
      s'.gpr .r9 = s.gpr .r9 - 48 ∧ (∀ q, q ≠ .r9 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [show Impl.Gcm.X86_64.StitchZH.midTest =
      [.alu .sub .r9 (.imm Impl.Gcm.X86_64.StitchZC.bigMinC)] ++
        [.alu .cmp .r9 (.imm (Impl.Gcm.X86_64.StitchZ.bigMinPE - Impl.Gcm.X86_64.StitchZC.bigMinC))] from rfl,
      WP.block_append_iff]
    refine WP.mono (subR9_ok s _ 48 e48) fun s₁ ⟨r₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_
    refine WP.mono (StitchZ.cmp_ok s₁ _ 96 e96) fun s₂ ⟨cf, g₂, l₂, m₂, rd₂, wr₂⟩ =>
      ⟨?_, by rw [g₂, r₁], fun q h => by rw [g₂, g₁ q h], fun x l => by rw [l₂, l₁], by rw [m₂, m₁],
        by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    rw [cf, r₁, BitVec.toNat_sub, show (48 : BitVec 64).toNat = 48 from rfl,
      show (BitVec.ofNat 64 96).toNat = 96 from rfl]
    congr 1
    exact decide_eq_decide.2 (by omega_using [])
  refine WP.seq (WP.mono (WP.hkeep (by decide) ht) fun s₁ ⟨⟨cf, r₁, g₁, l₁, m₁, rd₁, wr₁⟩, hh₁⟩ => ?_)
  have undo : ∀ c : Prog isa, (∀ t, ZFrame [] s t → HKeep s t → WP isa c t Q) →
      WP isa (.seq (.block Impl.Gcm.X86_64.StitchZH.midUndo) c) s₁ Q := fun c hc => by
    refine WP.seq (WP.mono (WP.hkeep (by decide) (addR9_ok s₁ _ 48 e48))
      fun s₂ ⟨⟨r₂, g₂, l₂, m₂, rd₂, wr₂⟩, hh₂⟩ => ?_)
    refine hc s₂ ⟨funext fun q => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
      fun x _ l _ => by rw [l₂, l₁]⟩ (hh₁.trans hh₂)
    by_cases hq : q = .r9
    · subst hq; rw [r₂, r₁, BitVec.sub_add_cancel]
    · rw [g₂ q hq, g₁ q hq]
  refine WP.ite (decide (48 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < 144)) (by simp only [eval, cf])
    (fun h => ?_) (fun h => ?_)
  · have h' := of_decide_eq_true h
    exact undo a (ha h'.1 h'.2)
  · exact undo b (hb (of_decide_eq_false h))

end VG.Proof.Gcm.X86_64.StitchZC
