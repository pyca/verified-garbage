module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPairE
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Gcm

/-!
# The 256-bit encryption loop: the blocks after the last group

`encR` is `enc` for any number of blocks from 16 on. Once its loop stops
with `r9 = 16 + r` (`Stitch.EInv`: the groups encrypted, all but the last
hashed), with `r` blocks left, `lastGR_ok` hashes the last group, as
`Stitch.final_ok` does, and moves `rdx` to the blocks after it (`EInvR`).
`remE_ok` then follows `remD_ok`, with the products of the ciphertext:
`StitchZH.remSetup_ok` stores the counter after all the blocks, `ksSel_ok`
computes the keystream of eight or sixteen blocks to `scratch + 256`, then
each block is encrypted and its ciphertext hashed, the first alone if their
number is odd and the rest two at a time (`remMidE_ok`, `RemPairE.lean`),
the products of the two lanes added, reduced into `Y`, and `Y` stored.
`encTailR_ok` is `encR` after its setup.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost EInv AInv Ready FinOk first_ok cmpE_ok body_ok final_ok ghRun_ok nb nr kp
  pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀ addr_eq in_sub in_sub_int in_rdwr blocks_ctr32
  blockAt_writeW_sep' store16_ok ghash_append16 GEnv ghFin)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE body first storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.StitchR (ks ksSel remE tailE encR)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInv accR accR_congr remSetup_ok zeroZ_ok keys_of)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- After the last group is encrypted and hashed: `rdx` at the `r` blocks
after it, `r9 = 16 + r`. -/
structure EInvR (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (16 + (nb s₀ - 16 * e))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀))
  y1 : s.lane .xmm2 1 = 0

/-- `add rdx, 256`. -/
theorem addRdx_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256)]) s fun s' =>
      s'.gpr .rdx = s.gpr .rdx + BitVec.ofNat 64 256 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.lane x l = s.lane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e256, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The last group hashed, as `Stitch.final_ok` does without the stores, and
`rdx` moved to the blocks after it. -/
theorem lastGR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (hgt : 16 * e < nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (lastG ++ ([.alu .add .rdx (.imm 256)] : List Instr))) s (EInvR s₀ P e) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  have hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr]
      r11 := by rw [f₂.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          hI.a.blocks _ (by omega_arith)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_arith, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₂.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₂.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, y41, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  have F : YFrame ([.xmm8, .xmm9, .xmm10] ++ ([.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] ++
      [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2])) s s₄ := f₂.comp (f₃.comp f₄)
  have hA₄ : AInv s₀ (16 * e) s₄ := hI.a.yframe F (by decide) (by decide) (by decide)
  refine WP.mono (addRdx_ok s₄) fun s₅ ⟨d₅, g₅, l₅, m₅, rd₅, wr₅⟩ => ?_
  have gk : ∀ q, q ≠ .rdx → s₅.gpr q = s.gpr q := fun q h => by rw [g₅ q h, F.gpr]
  have hm : s₅.mem = s.mem := by rw [m₅, F.mem]
  have hA₅ : AInv s₀ (16 * e) s₅ :=
    { le := hA₄.le
      ctr := fun l hl => by rw [l₅]; exact hA₄.ctr l hl
      msk := fun l hl => by rw [l₅]; exact hA₄.msk l hl
      inc := fun l hl => by rw [l₅]; exact hA₄.inc l hl
      rdi := by rw [g₅ _ (by decide)]; exact hA₄.rdi
      rsi := by rw [g₅ _ (by decide)]; exact hA₄.rsi
      r10 := by rw [g₅ _ (by decide)]; exact hA₄.r10
      frame := by rw [m₅]; exact hA₄.frame
      blocks := fun k hk => by rw [m₅]; exact hA₄.blocks k hk
      rd := by rw [rd₅]; exact hA₄.rd
      wr := by rw [wr₅]; exact hA₄.wr }
  refine
    { a := hA₅
      rdx := ?_, r9 := ?_, rax := by rw [gk _ (by decide)]; exact hI.rax
      gpr := fun q h1 h2 h3 h4 => by rw [gk q h2]; exact hI.gpr q h1 h2 h3 h4
      pw := fun k hk l hl => by rw [hm]; exact hI.pw k hk l hl
      m1 := fun l hl => by rw [l₅, F.lane _ (by decide) l hl]; exact hI.m1 l hl
      y := ?_, y1 := by rw [l₅]; exact y41 }
  · rw [d₅, F.gpr]
    apply BitVec.eq_of_toNat_eq
    have hd := (dp s₀).isLt
    rw [BitVec.toNat_add, BitVec.toNat_add, show (s.gpr .rdx).toNat = _ from ha, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 256 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show 256 * e < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [gk _ (by decide), hI.r9]
    congr 1; have := hI.a.le; omega_arith
  · rw [l₅, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y

theorem remE_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) {P : Nat → Nat → Block} (hr : RemLaw (hk s₀) P) {e : Nat}
    {s : State} (hI : EInvR s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa (remE .rdx) s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by omega_arith
  have hr15 : r ≤ 15 := by omega_arith
  have hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9, ← hr_def]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show remE .rdx = .seq (.block Impl.Gcm.X86_64.StitchZH.remSetup) (.seq ksSel
      (.seq (.block ((([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
          Impl.Gcm.X86_64.StitchAvx.zero) ++ ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)])
            (.block (Impl.Gcm.X86_64.StitchZH.remBody .rdx ++ Impl.Gcm.X86_64.StitchZH.remNext)))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (Impl.Gcm.X86_64.StitchR.remPairE .rdx ++
              Impl.Gcm.X86_64.StitchR.remNextPair)) .ne) (.block Impl.Gcm.X86_64.StitchR.foldLanes)))
            (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr) ++
              storeY)))))) from rfl]
  -- The counter after all the blocks, and the powers of the `r` blocks.
  refine WP.seq (WP.mono (remSetup_ok s hr1 hr15 hr9 (hI.a.msk 0 (by decide))
    (by rw [hI.rax, hI.a.wr]; exact in_sub_int hp.c_in (by omega_arith)))
    fun s₁ ⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩ => ?_)
  have e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hI.rax, e0] at m₁
  rw [hr11] at ax₁
  have lk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 2, s₁.lane x l = s.lane x l := fun x h l hl => by
    rw [← State.zlane_lt2 _ _ hl, z₁ x h l (by omega_arith), State.zlane_lt2 _ _ hl]
  have cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  have hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  have hrd₁ : s₁.rd = s₀.rd := by rw [rd₁]; exact hI.a.rd
  have hwr₁ : s₁.wr = s₀.wr := by rw [wr₁]; exact hI.a.wr
  have hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rdi
  -- The keystream.
  refine WP.seq (WP.mono (ksSel_ok hp hr1 hr15 (c := 16 * e) a10₁
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.inc l hl)
    (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
    (by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rsi) hrdi₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr11) hwr₁)
    fun s₂ ⟨ks₂, g₂, rd₂, wr₂, l₂, f₂⟩ => ?_)
  -- `r11` lowered, `r10 = 0`, the products cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preV_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  have gk₃ : ∀ q, q ≠ .r10 → q ≠ .r11 → q ≠ .rax → s₃.gpr q = s.gpr q := fun q h1 h11 h2 => by
    rw [g₃ q h11 h1, g₂ q h1, g₁ q h1 h2]
  have lk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 2, s₃.lane x l = s.lane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₃ x h8 h9 h10 l (by omega_arith), State.zlane_lt2 _ _ hl, l₂ x h13 h14 ha l hl,
      lk₁ x h13 l hl]
  have h11₃ : s₃.gpr .r11 = pp s₀ - BitVec.ofNat 64 512 := by
    rw [d₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), hr11]
  have eK : ∀ j, pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j) =
      pp s₀ + BitVec.ofNat 64 (256 + 16 * j) := fun j => by
    rw [show 768 + 16 * j = 512 + (256 + 16 * j) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀ - BitVec.ofNat 64 512)
    (pp s₀ + BitVec.ofNat 64 (256 - 16 * r)) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  have hE : E.Ok :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA, gP := h11₃
      gW := by show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      inS := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inK := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j < r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 16
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega_arith)
      inW := fun j (hj : j < r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 16
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [eK]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)) }
  have hI₃ : RInv E 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := by
        obtain ⟨a, b, c⟩ := p₃ 0 (by decide)
        simp only [prod, State.proj_xmm, ← State.zlane_lt2 _ _ (show 0 < 2 by decide), a, b, c]
        rfl
      y := rfl
      m0 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.a.msk 0 (by decide)
      m1 := by
        rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
        exact hI.m1 0 (by decide) }
  have hE2 : Ok2 E :=
    { inS := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inK := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 32
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j + 2 ≤ r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega_arith)
      inW := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith)) }
  have z1 : ∀ x, s₃.zlane x 1 = 0 → s₃.lane x 1 = 0 := fun x h => by rw [← State.zlane_lt2 _ _ (by decide)]; exact h
  -- The first block alone if `r` is odd, then the pairs and their lanes added.
  refine remMidE_ok (E := E) hE hE2 hI₃ (z1 _ (p₃ 1 (by decide)).1) (z1 _ (p₃ 1 (by decide)).2.1)
    (z1 _ (p₃ 1 (by decide)).2.2)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]; exact hI.y1)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]
        exact hI.a.msk 1 (by decide)) fun s₄ hI₄ => ?_
  -- The products reduced into `Y`, `r11` restored, and `Y` stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add11_ok s₅) fun s₆ ⟨a11, g₆, l₆, m₆, rd₆, wr₆⟩ => ?_
  have hrcx : s₆.gpr .rcx = yp s₀ := by
    rw [g₆ _ (by decide), f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  have m06 : s₆.lane .xmm0 0 = revMask := by
    rw [l₆, f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₆ m06
    (by rw [hrcx, wr₆, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, l₆, y₅] at m₇
  have hm₆ : s₆.mem = s₄.mem := by rw [m₆, f₅.mem]
  have hnb : nb s₀ = 16 * e + r := by omega_arith
  -- What the stages keep of the memory before them.
  have toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) →
      Region.Disjoint ⟨p, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  have ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  have hS : ∀ j < r, blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) :=
    fun j hj => by
      have hk : 16 * e + j < nb s₀ := by omega_arith
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk]
      simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The ciphertext of the blocks after the last group.
  have hX : ∀ j < r, E.X j = ctb s₀ (16 * e + j) := fun j hj => by
    show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [hS j hj, eK, m₃, ks₂ j hj]
  -- The blocks.
  have hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      have hj : j < r := by omega_arith
      have ct := hI₄.ct j hj
      have eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct, hX j hj]
  have hT : ∀ j < r, E.T j = P ((16 - r + j) / 2) ((16 - r + j) % 2) := fun j hj => by
    show s₃.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * r) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [Offset.add_add, show 256 - 16 * r + 16 * j = 32 * ((16 - r + j) / 2) + 16 * ((16 - r + j) % 2) by omega_arith,
      m₃, f₂.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (32 * ((16 - r + j) / 2) + 16 * ((16 - r + j) % 2)), 16⟩)
        (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      m₁, Mem.readW_writeW_sep ((hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))).sep
          (Region.contains_self _ _) cw) (by decide)]
    exact hI.pw _ (by omega_arith) _ (by omega_arith)
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  have hb : ∀ k < nb s₀, blockAt s₇.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, hm₆, hb₄ k hk]
  have fA : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  have hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) := by
    rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show blockAt s₇.mem (cp s₀) = _
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl, hm₆,
      blockAt_frame hI₄.frame (fA _ hp.d_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide), Nat.add_zero,
      VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₇.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₇.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₇.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    rw [hbl, m₇, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.prod, accR_congr _ r hX hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₇.mem
    have F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    have F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    have F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    have F3 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    rw [m₇, hm₆]
    exact (((F0.trans F1).trans F2).trans F3).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₇.gpr q = _
    by_cases h11 : q = .r11
    · subst h11
      rw [g₇, a11, f₅.gpr, hI₄.gpr _ (by decide) (by decide)]
      show s₃.gpr .r11 + BitVec.ofNat 64 512 = _
      rw [h11₃, BitVec.sub_add_cancel]
    · rw [g₇, g₆ q h11, f₅.gpr, hI₄.gpr q h3 h4]
      show s₃.gpr q = _
      rw [gk₃ q h4 h11 h1]
      exact hI.gpr q h1 h2 h3 h4
  · show s₇.rd = _
    rw [rd₇, rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₇.wr = _
    rw [wr₇, wr₆, f₅.wr, hI₄.wr]; exact hwr₃

/-- The encryption loop, for any number of blocks from 16 on: it stops with
`16 + r` blocks left, `r < 16`. -/
theorem loopER_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' =>
      ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e s' := by
  have fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, he, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI'⟩
    have := hI.a.le
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega_arith, hI⟩

/-- `cmp r9, 16` after the loop. -/
theorem cmpE16_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s)
    (hlt : nb s₀ - 16 * (e - 1) < 32) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.zf = some (decide (nb s₀ = 16 * e)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.mono (cmp916_ok s) fun s' ⟨z, g, l, m, rd, wr⟩ => ⟨?_, ?_⟩
  · have yf : YFrame [] s s' := ⟨g, m, rd, wr, fun x _ l' hl => l x l'⟩
    exact ⟨hI.a.yframe yf (by simp) (by simp) (by simp), hI.one, by rw [g]; exact hI.rdx, by rw [g]; exact hI.r9,
      by rw [g]; exact hI.rax, fun r h1 h2 h3 h4 => by rw [g]; exact hI.gpr r h1 h2 h3 h4,
      fun k hk l' hl => by rw [m]; exact hI.pw k hk l' hl, fun l' hl => by rw [l]; exact hI.m1 l' hl,
      by rw [l]; exact hI.y, by rw [l]; exact hI.y1⟩
  · rw [z, hI.r9, show nb s₀ - 16 * (e - 1) = 16 + (nb s₀ - 16 * e) by omega_arith, zero16 _ (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩

/-- `tailE`, in place, once the loop has stopped. -/
theorem tailER_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P)
    (hr : RemLaw (hk s₀) P) {e : Nat} {s : State} (hlt : nb s₀ - 16 * (e - 1) < 32) (hI : EInv s₀ P e s) :
    WP isa (tailE [] .rdx) s (EPost s₀) := by
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (cmpE16_ok hI hlt) fun s₁ ⟨hI₁, z₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_)
  · exact final_ok hp hf (by simpa using h) hI₁
  · have hne : nb s₀ ≠ 16 * e := by simpa using h
    rw [List.append_nil]
    exact WP.seq (WP.mono (lastGR_ok hp hf (by omega_arith) hI₁) fun s₂ hI₂ =>
      remE_ok hp hr hI₂ (by omega_arith) hne)

/-- `encR` after the setup, for any number of blocks from 16 on. -/
theorem encTailR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P)
    (hr : RemLaw (hk s₀) P) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (tailE [] .rdx)))) s (EPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopER_ok hp hf hI₃ hcf) fun s₄ ⟨e, hlt, hI₄⟩ => tailER_ok hp hf hr hlt hI₄)

end VG.Proof.Gcm.X86_64.StitchR
