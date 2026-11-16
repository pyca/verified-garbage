module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Rem
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemPairE
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemSetup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Ks
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGD
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Powers
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Rem

/-!
# The 256-bit loops: the blocks after the last group

`encR` is `enc` for any number of blocks from 16 on. Once its loop stops
with `r9 = 16 + r` (`Stitch.EInv`: the groups encrypted, all but the last
hashed), with `r` blocks left, `lastGR_ok` hashes the last group, as
`Stitch.final_ok` does, and moves `rdx` to the blocks after it (`EInvR`).
`remE_okF` then stores the counter after all the blocks and points `rax` at
the powers of the `r` blocks in the key context (`remSetupC_ok`, `CtxPow`),
computes the keystream of eight or sixteen blocks to `scratch + 256`
(`ksSel_ok`), then encrypts each block and hashes its ciphertext, the first
alone if their number is odd and the rest two at a time (`remMidC_ok`,
`RemPairE.lean`), adds the products of the two lanes, reduces them into `Y`,
clears the keystream (`zeroKs_ok`) and stores `Y`. `encTailR_ok` is `encR`
after its setup.

`remD_okF` does the same for decryption, from the state the decryption loop
stops in with `r9` raised by 16 (`DInvR`), hashing the blocks as read
(`remMidDC_ok`); `dtailR_okF` is the end of `decR` after its loop
(`StitchR.tailD`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost DInv EInv AInv Ready FinOk first_ok cmpE_ok body_ok final_ok ghRun_ok nb nr kp
  pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀ addr_eq in_sub in_sub_int in_rdwr blocks_ctr32
  blockAt_writeW_sep' store16_ok ghash_append16 GEnv ghFin)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE body first storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.StitchR (ks ksSel remD remE tailE encR)
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
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    State.setReg, e256, ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The last group hashed, as `Stitch.final_ok` does without the stores, and
`rdx` moved to the blocks after it. -/
theorem lastGR_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (hgt : 16 * e < nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (lastG ++ ([.alu .add .rdx (.imm 256)] : List Instr))) s fun s' =>
      EInvR s₀ P e s' ∧ s'.mem = s.mem := by
  have hw := hp.wrap_d
  have h1e := hI.one
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  obtain hE₂ : GEnv s₀ 0 a X P s₂ :=
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
  obtain F : YFrame ([.xmm8, .xmm9, .xmm10] ++ ([.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] ++
      [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2])) s s₄ := f₂.comp (f₃.comp f₄)
  obtain hA₄ : AInv s₀ (16 * e) s₄ := hI.a.yframe F (by decide) (by decide) (by decide)
  refine WP.mono (addRdx_ok s₄) fun s₅ ⟨d₅, g₅, l₅, m₅, rd₅, wr₅⟩ => ?_
  obtain gk : ∀ q, q ≠ .rdx → s₅.gpr q = s.gpr q := fun q h => by rw [g₅ q h, F.gpr]
  obtain hm : s₅.mem = s.mem := by rw [m₅, F.mem]
  obtain hA₅ : AInv s₀ (16 * e) s₅ :=
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
  refine ⟨
    { a := hA₅
      rdx := ?_, r9 := ?_, rax := by rw [gk _ (by decide)]; exact hI.rax
      gpr := fun q h1 h2 h3 h4 => by rw [gk q h2]; exact hI.gpr q h1 h2 h3 h4
      pw := fun k hk l hl => by rw [hm]; exact hI.pw k hk l hl
      m1 := fun l hl => by rw [l₅, F.lane _ (by decide) l hl]; exact hI.m1 l hl
      y := ?_, y1 := by rw [l₅]; exact y41 }, hm⟩
  · rw [d₅, F.gpr]
    apply BitVec.eq_of_toNat_eq
    obtain hd := (dp s₀).isLt
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

theorem lastGR_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (hgt : 16 * e < nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (lastG ++ ([.alu .add .rdx (.imm 256)] : List Instr))) s (EInvR s₀ P e) :=
  WP.mono (lastGR_okF hp hf hgt hI) fun _ h => h.1

/-! ## The powers from the key context, and the keystream cleared -/

/-- What `remE` needs of the key context, which it reads after storing the
counter and the keystream: its first 512 bytes, holding the first eight
prepared pairs, accessible and apart from the data `D` it writes, the working
space and the counter. -/
structure CtxPow (s₀ : State) (D : Region) : Prop where
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 512
  wrap_k : (kp s₀).toNat + 512 ≤ 2 ^ 64
  d_k : D.Disjoint ⟨kp s₀, 512⟩
  p_k : (pR s₀).Disjoint ⟨kp s₀, 512⟩
  c_k : (cR s₀).Disjoint ⟨kp s₀, 512⟩
  pow : Stitch.PowersN 8 s₀.mem (kp s₀)

/-- The powers the prepared pairs hold, as the setup loads them (`H'¹⁶⁻²ᵏ⁻ˡ`
in lane `l` of pair `k`). -/
abbrev powC (s₀ : State) (k l : Nat) : Block := StitchZP.hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))

/-- The power of the last but `e - 1` block, `H'ᵉ`, at `224 + 16 e`, or `32`
more for odd `e`. -/
theorem ctxPow_at {s₀ : State} {D : Region} (hc : CtxPow s₀ D) {e : Nat} (h1 : 1 ≤ e) (h15 : e ≤ 15) :
    s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (224 + 16 * e + 32 * (e % 2))) 128 =
      StitchZP.hInvF (Spec.Gcm.hpow (hk s₀) e) := by
  rcases Nat.mod_two_eq_zero_or_one e with h | h
  · have := StitchZR.pair_values hc.pow (j := e - 1) (by omega_arith) (by omega_arith) (l := 0) (by decide)
    rw [show 240 + 16 * (e - 1) + 16 * 0 = 224 + 16 * e + 32 * (e % 2) by omega_arith,
      show e - 1 + 1 - 0 = e by omega_arith] at this
    exact this
  · have := StitchZR.pair_values hc.pow (j := e) (by omega_arith) h (l := 1) (by decide)
    rw [show 240 + 16 * e + 16 * 1 = 224 + 16 * e + 32 * (e % 2) by omega_arith, Nat.add_sub_cancel] at this
    exact this

/-- `remAlu2`, with `rax` at `rdi + 224 + 16 r`. -/
theorem remAlu2C_ok (s : State) {r : Nat} (h15 : r ≤ 15) (h10 : s.gpr .r10 = BitVec.ofNat 64 r) :
    WP isa (.block [.alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .alu .add .r10 (.reg .r10), .mov .rax (.reg .rdi), .alu .add .rax (.imm 224), .alu .add .rax (.reg .r10)])
      s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * r) ∧
      s'.gpr .rax = s.gpr .rdi + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * r) ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain e224 : BitVec.signExtend 64 (224 : BitVec 32) = BitVec.ofNat 64 224 := by decide
  obtain x16 : BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r)) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r) +
      (BitVec.ofNat 64 r + BitVec.ofNat 64 r + (BitVec.ofNat 64 r + BitVec.ofNat 64 r))) =
      BitVec.ofNat 64 (16 * r) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega_arith
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, State.setReg, e224, h10, x16, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ↓reduceIte], fun _ _ => rfl, trivial, trivial,
    trivial⟩

/-- `StitchZH.remSetup_ok` for `remSetupC`: `rax` at `rdi + 224 + 16 r`. -/
theorem remSetupC_ok (s : State) {r : Nat} (h1 : 1 ≤ r) (h15 : r ≤ 15)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r)) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.remSetupC) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int))
        (XBinOp.eval .pshufb (Nat.repeat inc32 r (s.lane .xmm14 0)) revMask) ∧
      s'.gpr .r10 = BitVec.ofNat 64 (16 * r) ∧
      s'.gpr .rax = s.gpr .rdi + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * r) ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm13 → ∀ l < 4, s'.zlane x l = s.zlane x l) := by
  rw [Impl.Gcm.X86_64.StitchR.remSetupC, show ([.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16), .vop (.vmovq .xmm13 .r10),
      .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0),
      .vmovdquStore .l128 (at_ .rax 0) .xmm13,
      .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .mov .rax (.reg .rdi), .alu .add .rax (.imm 224), .alu .add .rax (.reg .r10)] : List Instr) =
    [.mov .r10 (.reg .r9), .alu .sub .r10 (.imm 16)] ++ ([.vop (.vmovq .xmm13 .r10),
      .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm13), .vop (.vbin .vpshufb .l128 .xmm13 .xmm13 .xmm0)] ++
      ([.vmovdquStore .l128 (at_ .rax 0) .xmm13] ++
      [.alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .mov .rax (.reg .rdi), .alu .add .rax (.imm 224), .alu .add .rax (.reg .r10)])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (StitchZH.remAlu1_ok s h15 h9) fun s₁ ⟨a₁, g₁, z₁, l₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchZH.remCtr_ok s₁ (r := r) (by omega_arith) a₁ (by rw [l₁]; exact h0)) fun s₂ ⟨c₂, f₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchZH.store16_ok .xmm13 .rax s₂ (by
      rw [f₂.gpr, f₂.wr, g₁ _ (by decide), wr₁]; exact hin)) fun s₃ ⟨m₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  refine WP.mono (remAlu2C_ok s₃ h15 (by rw [g₃, f₂.gpr, a₁])) fun s' ⟨a', ax', g', z', m', rd', wr'⟩ =>
    ⟨?_, a', ?_, fun q h1 h2 => ?_, by rw [rd', rd₃, f₂.rd, rd₁], by rw [wr', wr₃, f₂.wr, wr₁],
      fun x hx l hl => ?_⟩
  · rw [m', m₃, f₂.gpr, f₂.mem, m₁, g₁ _ (by decide), show s₂.xmm .xmm13 = s₂.lane .xmm13 0 from rfl, c₂, l₁]
  · rw [ax', g₃, f₂.gpr, g₁ _ (by decide)]
  · rw [g' q h1 h2, g₃, f₂.gpr, g₁ q h1]
  · rw [z', z₃, f₂.zlane x (by simp [hx]) l hl, z₁]

/-- `zeroKs`: the keystream `remE` stored at `r11 + 256`, of eight blocks, or
sixteen if `r > 8` (`r10 = 16 r`), cleared. -/
theorem zeroKs_ok {s : State} {r : Nat} (h15 : r ≤ 15) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hin : InRegions s.wr (s.gpr .r11) 1024) (hw : (s.gpr .r11).toNat + 1024 ≤ 2 ^ 64) :
    WP isa Impl.Gcm.X86_64.StitchR.zeroKs s fun s' =>
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem ∧
      (∀ k < (if r ≤ 8 then 8 else 16), blockAt s'.mem (s.gpr .r11 + BitVec.ofNat 64 (256 + 16 * k)) = 0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ x, x ≠ .xmm12 → ∀ l < 2, s'.lane x l = s.lane x l) := by
  obtain stK : ∀ (j : Nat) (t : State), 32 * j + 128 ≤ 1024 → t.gpr .r11 = s.gpr .r11 → t.wr = s.wr →
      (∀ l < 2, t.lane .xmm12 l = 0) →
      WP isa (.block (Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) j)) t fun t' =>
        (∀ k < 8, blockAt t'.mem (s.gpr .r11 + BitVec.ofNat 64 (32 * j + 16 * k)) = 0) ∧
        Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 128⟩] t.mem t'.mem ∧
        t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ x l, t'.lane x l = t.lane x l) := by
    intro j t hj g w z
    refine WP.mono (Stitch.storesK_ok .r11 (List.replicate 4 .xmm12) j t (fun k hk => by
        rw [w, g]; exact Stitch.in_sub_int hin (by simp at hk; omega_arith))
      (by rw [g]; simp; omega_arith)) fun t' ⟨sv, fr, g', rd', wr', l'⟩ => ?_
    rw [g, show 32 * (List.replicate 4 XReg.xmm12).length = 128 by simp] at fr
    refine ⟨fun k hk => ?_, fr, g', rd', wr', l'⟩
    have := sv (k / 2) (by simp; omega_arith) (k % 2) (by omega_arith)
    rw [g, show 32 * (j + k / 2) + 16 * (k % 2) = 32 * j + 16 * k by omega_arith, List.getElem_replicate,
      z _ (by omega_arith)] at this
    rw [VG.Proof.Gcm.X86_64.blockAt_eq, this]; rfl
  unfold Impl.Gcm.X86_64.StitchR.zeroKs
  refine WP.seq ?_
  rw [show (.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12) :: Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) 8 :
      List Instr) = [.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12)] ++ Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) 8
    from rfl, WP.block_append_iff]
  refine WP.mono (Stitch.zero12_ok s) fun s₁ ⟨z₁, k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (stK 8 s₁ (by decide) (by rw [g₁]) wr₁ z₁) fun s₂ ⟨v₂, f₂, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [m₁] at f₂
  refine WP.seq (WP.mono (StitchZH.cmp10_ok s₂ 129 129 (by decide)) fun s₃ ⟨c₃, g₃, l₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain t16 : (s₂.gpr .r10).toNat = 16 * r := by rw [g₂, g₁, h10, toNat_ofNat_lt (by omega_arith)]
  rw [t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at c₃
  obtain e1 : ∀ x l, l < 2 → s₃.lane x l = s₂.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₃]
  obtain sub1 : Region.Sub ⟨s.gpr .r11 + BitVec.ofNat 64 (32 * 8), 128⟩ ⟨s.gpr .r11 + BitVec.ofNat 64 256, 256⟩ :=
    Offset.sub _ (by decide) (by decide)
  obtain sub2 : Region.Sub ⟨s.gpr .r11 + BitVec.ofNat 64 (32 * 12), 128⟩ ⟨s.gpr .r11 + BitVec.ofNat 64 256, 256⟩ :=
    Offset.sub _ (by decide) (by decide)
  obtain F2 : Frame [⟨s.gpr .r11 + BitVec.ofNat 64 256, 256⟩] s.mem s₂.mem :=
    f₂.sub fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, List.mem_singleton_self _, sub1⟩
  obtain kl : ∀ x, x ≠ .xmm12 → ∀ l < 2, s₃.lane x l = s.lane x l := fun x h l hl => by
    rw [e1 x l hl, l₂, k₁ x h l hl]
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, c₃]) (fun h => ?_) (fun h => ?_)
  · have hr8 : r ≤ 8 := by simp at h; omega_arith
    refine WP.block_nil ⟨by rw [m₃]; exact F2, fun k hk => ?_, by rw [g₃, g₂, g₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁], kl⟩
    simp only [hr8, ite_true] at hk
    rw [m₃, show 256 + 16 * k = 32 * 8 + 16 * k by omega_arith]; exact v₂ k hk
  · have hr8 : ¬ r ≤ 8 := by simp at h; omega_arith
    refine WP.mono (stK 12 s₃ (by decide) (by rw [g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁])
        (fun l hl => by rw [e1 _ l hl, l₂]; exact z₁ l hl))
      fun s₄ ⟨v₄, f₄, g₄, rd₄, wr₄, l₄⟩ => ⟨?_, fun k hk => ?_, by rw [g₄, g₃, g₂, g₁],
        by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], fun x h l hl => by rw [l₄]; exact kl x h l hl⟩
    · rw [m₃] at f₄
      exact F2.trans (f₄.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, List.mem_singleton_self _, sub2⟩)
    · simp only [hr8, ite_false] at hk
      by_cases hk8 : k < 8
      · rw [blockAt_frame f₄ (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), m₃,
          show 256 + 16 * k = 32 * 8 + 16 * k by omega_arith]
        exact v₂ k hk8
      · rw [show 256 + 16 * k = 32 * 12 + 16 * (k - 8) by omega_arith]; exact v₄ (k - 8) (by omega_arith)

/-- `zeroKs`, byte by byte: the 128 bytes at `r11 + 256`, or 256 if `r > 8`,
cleared, and only those 128 written if `r ≤ 8`. -/
theorem zeroKs_bytes {s : State} {r : Nat} (h15 : r ≤ 15) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * r))
    (hin : InRegions s.wr (s.gpr .r11) 1024) (hw : (s.gpr .r11).toNat + 1024 ≤ 2 ^ 64) :
    WP isa Impl.Gcm.X86_64.StitchR.zeroKs s fun s' =>
      (r ≤ 8 → Frame [⟨s.gpr .r11 + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem) ∧
      ∀ i < (if r ≤ 8 then 128 else 256), s'.mem (s.gpr .r11 + BitVec.ofNat 64 (256 + i)) = 0 := by
  obtain stK : ∀ (j : Nat) (t : State), 32 * j + 128 ≤ 1024 → t.gpr .r11 = s.gpr .r11 → t.wr = s.wr →
      (∀ l < 2, t.lane .xmm12 l = 0) →
      WP isa (.block (Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) j)) t fun t' =>
        (∀ i < 128, t'.mem (s.gpr .r11 + BitVec.ofNat 64 (32 * j + i)) = 0) ∧
        Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 128⟩] t.mem t'.mem ∧
        t'.gpr = t.gpr ∧ t'.wr = t.wr ∧ (∀ x l, t'.lane x l = t.lane x l) := by
    intro j t hj g w z
    refine WP.mono (Stitch.storesK_ok .r11 (List.replicate 4 .xmm12) j t (fun k hk => by
        rw [w, g]; exact Stitch.in_sub_int hin (by simp at hk; omega_arith))
      (by rw [g]; simp; omega_arith)) fun t' ⟨sv, fr, g', _, wr', l'⟩ => ?_
    rw [g, show 32 * (List.replicate 4 XReg.xmm12).length = 128 by simp] at fr
    refine ⟨fun i hi => ?_, fr, g', wr', l'⟩
    obtain v := sv (i / 32) (by simp; omega_arith) ((i % 32) / 16) (by omega_arith)
    rw [g, List.getElem_replicate, z _ (by omega_arith)] at v
    rw [show s.gpr .r11 + BitVec.ofNat 64 (32 * j + i) =
        s.gpr .r11 + BitVec.ofNat 64 (32 * (j + i / 32) + 16 * (i % 32 / 16)) + BitVec.ofNat 64 (i % 16) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith,
      Stitch.byte_readW128 t'.mem _ (j := i % 16) (by omega_arith), v]
    simp
  unfold Impl.Gcm.X86_64.StitchR.zeroKs
  refine WP.seq ?_
  rw [show (.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12) :: Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) 8 :
      List Instr) = [.vop (.vbin .vpxor .l128 .xmm12 .xmm12 .xmm12)] ++ Impl.Gcm.X86_64.Stitch.storesK .r11 (List.replicate 4 .xmm12) 8
    from rfl, WP.block_append_iff]
  refine WP.mono (Stitch.zero12_ok s) fun s₁ ⟨z₁, _, g₁, m₁, _, wr₁⟩ => ?_
  refine WP.mono (stK 8 s₁ (by decide) (by rw [g₁]) wr₁ z₁) fun s₂ ⟨v₂, f₂, g₂, wr₂, l₂⟩ => ?_
  rw [m₁] at f₂
  refine WP.seq (WP.mono (StitchZH.cmp10_ok s₂ 129 129 (by decide)) fun s₃ ⟨c₃, g₃, l₃, m₃, _, wr₃⟩ => ?_)
  obtain t16 : (s₂.gpr .r10).toNat = 16 * r := by rw [g₂, g₁, h10, toNat_ofNat_lt (by omega_arith)]
  rw [t16, show (BitVec.ofNat 64 129).toNat = 129 from rfl] at c₃
  obtain e1 : ∀ x l, l < 2 → s₃.lane x l = s₂.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₃]
  refine WP.ite (decide (16 * r < 129)) (by simp only [eval, c₃]) (fun h => ?_) (fun h => ?_)
  · have hr8 : r ≤ 8 := by simp at h; omega_arith
    refine WP.block_nil ⟨fun _ => by rw [m₃]; exact f₂, fun i hi => ?_⟩
    simp only [hr8, ite_true] at hi
    rw [m₃, show 256 + i = 32 * 8 + i by omega_arith]; exact v₂ i hi
  · have hr8 : ¬ r ≤ 8 := by simp at h; omega_arith
    refine WP.mono (stK 12 s₃ (by decide) (by rw [g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁])
        (fun l hl => by rw [e1 _ l hl, l₂]; exact z₁ l hl))
      fun s₄ ⟨v₄, f₄, _, _, _⟩ => ⟨fun h => absurd h hr8, fun i hi => ?_⟩
    simp only [hr8, ite_false] at hi
    by_cases hk : i < 128
    · rw [f₄ _ (fun r' hr' hc => ?_), m₃, show 256 + i = 32 * 8 + i by omega_arith]
      · exact v₂ i hk
      · simp only [List.mem_singleton] at hr'; subst hr'
        change (s.gpr .r11 + BitVec.ofNat 64 (256 + i) - (s.gpr .r11 + BitVec.ofNat 64 (32 * 12))).toNat < 128 at hc
        rw [Offset.lt_iff _ _ (by omega_arith), Mem.sub_ofNat_toNat _ (by omega_arith)] at hc
        omega_arith
    · rw [show 256 + i = 32 * 12 + (i - 128) by omega_arith]; exact v₄ (i - 128) (by omega_arith)

/-- `remE_ok`, and what `remE` leaves at `scratch + 256`, where it puts the
keystream: its first 128 bytes, and the next 128 if `r > 8`, cleared, and
nothing else written but the counter, `Y` and the data. -/
theorem remE_okF {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (hc : CtxPow s₀ (dR s₀)) (hr : RemLaw (hk s₀) (powC s₀))
    {P : Nat → Nat → Block} {e : Nat}
    {s : State} (hI : EInvR s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa (remE .rdx) s fun s' => EPost s₀ s' ∧
      Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem ∧
      ∀ i < 256, s'.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) =
        if i < 128 ∨ 8 < nb s₀ - 16 * e then 0 else s.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  obtain hr1 : 1 ≤ r := by omega_arith
  obtain hr15 : r ≤ 15 := by omega_arith
  obtain hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9, ← hr_def]
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show remE .rdx = .seq (.block Impl.Gcm.X86_64.StitchR.remSetupC) (.seq ksSel
      (.seq (.block ((([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
          Impl.Gcm.X86_64.StitchAvx.zero) ++ ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)])
            (.block (Impl.Gcm.X86_64.StitchR.remOneC .rdx)))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (Impl.Gcm.X86_64.StitchR.remPairE .rdx ++
              [.alu .sub .rax (.imm 64)] ++ Impl.Gcm.X86_64.StitchR.remNextPair)) .ne)
              (.block Impl.Gcm.X86_64.StitchR.foldLanes)))
            (.seq (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr)))
              (.seq Impl.Gcm.X86_64.StitchR.zeroKs (.block storeY))))))) from rfl]
  -- The counter after all the blocks, and `rax` at the powers of the `r` blocks in the key context.
  refine WP.seq (WP.mono (remSetupC_ok s hr1 hr15 hr9 (hI.a.msk 0 (by decide))
    (by rw [hI.rax, hI.a.wr]; exact in_sub_int hp.c_in (by omega_arith)))
    fun s₁ ⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩ => ?_)
  obtain e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hI.rax, e0] at m₁
  rw [hI.a.rdi] at ax₁
  obtain lk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 2, s₁.lane x l = s.lane x l := fun x h l hl => by
    rw [← State.zlane_lt2 _ _ hl, z₁ x h l (by omega_arith), State.zlane_lt2 _ _ hl]
  obtain cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  obtain hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  obtain hrd₁ : s₁.rd = s₀.rd := by rw [rd₁]; exact hI.a.rd
  obtain hwr₁ : s₁.wr = s₀.wr := by rw [wr₁]; exact hI.a.wr
  obtain hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rdi
  -- The keystream.
  refine WP.seq (WP.mono (ksSel_okF hp hr1 hr15 (c := 16 * e) a10₁
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.inc l hl)
    (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
    (by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rsi) hrdi₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr11) hwr₁)
    fun s₂ ⟨⟨ks₂, g₂, rd₂, wr₂, l₂, f₂⟩, f₂'⟩ => ?_)
  -- `r11` lowered, `r10 = 0`, the products cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preV_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  obtain gk₃ : ∀ q, q ≠ .r10 → q ≠ .r11 → q ≠ .rax → s₃.gpr q = s.gpr q := fun q h1 h11 h2 => by
    rw [g₃ q h11 h1, g₂ q h1, g₁ q h1 h2]
  obtain lk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 2, s₃.lane x l = s.lane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₃ x h8 h9 h10 l (by omega_arith), State.zlane_lt2 _ _ hl, l₂ x h13 h14 ha l hl,
      lk₁ x h13 l hl]
  obtain h11₃ : s₃.gpr .r11 = pp s₀ - BitVec.ofNat 64 512 := by
    rw [d₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), hr11]
  obtain eK : ∀ j, pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j) =
      pp s₀ + BitVec.ofNat 64 (256 + 16 * j) := fun j => by
    rw [show 768 + 16 * j = 512 + (256 + 16 * j) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  obtain hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀ - BitVec.ofNat 64 512)
    (kp s₀ + BitVec.ofNat 64 224) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hwk := hc.wrap_k
  obtain eC : ∀ j, j < r → E.aC j = kp s₀ + BitVec.ofNat 64 (224 + 16 * (r - j) + 32 * ((r - j) % 2)) := fun j _ => by
    show kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - j) + 32 * ((r - j) % 2)) = _
    rw [Offset.add_add, Nat.add_assoc]
  obtain kD : ∀ {d n : Nat}, d + n ≤ 512 → Region.Disjoint ⟨kp s₀ + BitVec.ofNat 64 d, n⟩ ⟨bAddr s₀ (16 * e), 16 * r⟩ :=
    fun {d n} h => (hc.d_k.symm.sub_left (Offset.sub_base _ h)).sub_right
      (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  obtain hE : OkC E :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA, gP := h11₃
      gW := by
        show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      srcA := by show Reg.rdx ≠ Reg.rax; decide
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
        rw [eC j hj, show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith)
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [eK]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < r) => by
        rw [eC j hj]; exact kD (by omega_arith)
      inS2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inK2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 32
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega_arith)
      inW2 := fun j (hj : j + 2 ≤ r) (hev : (r - j) % 2 = 0) => by
        rw [eC j (by omega_arith), show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith) }
  obtain hI₃ : RInvC E E.X 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      ax := by
        show s₃.gpr .rax + s₃.gpr .r10 = kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - 0))
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁, z₃, Nat.sub_zero]
        exact BitVec.add_zero _
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ _ => rfl, rd := rfl, wr := rfl
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
  obtain z1 : ∀ x, s₃.zlane x 1 = 0 → s₃.lane x 1 = 0 := fun x h => by rw [← State.zlane_lt2 _ _ (by decide)]; exact h
  -- The first block alone if `r` is odd, then the pairs and their lanes added.
  refine remMidC_ok (E := E) hE hI₃ (z1 _ (p₃ 1 (by decide)).1) (z1 _ (p₃ 1 (by decide)).2.1)
    (z1 _ (p₃ 1 (by decide)).2.2)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]; exact hI.y1)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]
        exact hI.a.msk 1 (by decide)) fun s₄ hI₄ => ?_
  -- The products reduced into `Y`, `r11` restored, the keystream cleared, and `Y` stored.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  refine WP.mono (add11_ok s₅) fun s₅a ⟨a11, g₅a, l₅a, m₅a, rd₅a, wr₅a⟩ => ?_
  obtain h11₅a : s₅a.gpr .r11 = pp s₀ := by
    rw [a11, f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .r11 + BitVec.ofNat 64 512 = _
    rw [h11₃, BitVec.sub_add_cancel]
  obtain h10₅a : s₅a.gpr .r10 = BitVec.ofNat 64 (16 * r) := by
    rw [g₅a _ (by decide), f₅.gpr, hI₄.r10]
  obtain hin₅ : InRegions s₅a.wr (s₅a.gpr .r11) 1024 := by
    rw [h11₅a, wr₅a, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.p_in
  refine WP.seq (WP.mono (Stitch.wp_and (zeroKs_ok (r := r) hr15 h10₅a hin₅ (by rw [h11₅a]; exact hwp))
    (zeroKs_bytes (r := r) hr15 h10₅a hin₅ (by rw [h11₅a]; exact hwp)))
    fun s₆ ⟨⟨fz, zz, gz, rdz, wrz, lz⟩, fz', zb⟩ => ?_)
  rw [h11₅a] at fz zz fz' zb
  obtain g₆ : ∀ q, q ≠ .r11 → s₆.gpr q = s₅.gpr q := fun q h => by rw [gz, g₅a q h]
  obtain l₆ : ∀ x, x ≠ .xmm12 → ∀ l < 2, s₆.lane x l = s₅.lane x l := fun x h l hl => by rw [lz x h l hl, l₅a]
  obtain rd₆ : s₆.rd = s₅.rd := by rw [rdz, rd₅a]
  obtain wr₆ : s₆.wr = s₅.wr := by rw [wrz, wr₅a]
  obtain a11' : s₆.gpr .r11 = pp s₀ := by rw [gz, h11₅a]
  obtain hrcx : s₆.gpr .rcx = yp s₀ := by
    rw [g₆ _ (by decide), f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  obtain m06 : s₆.lane .xmm0 0 = revMask := by
    rw [l₆ _ (by decide) 0 (by decide), f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₆ m06
    (by rw [hrcx, wr₆, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, l₆ _ (by decide) 0 (by decide), y₅] at m₇
  obtain hm₅a : s₅a.mem = s₄.mem := by rw [m₅a, f₅.mem]
  rw [hm₅a] at fz fz'
  obtain hnb : nb s₀ = 16 * e + r := by omega_arith
  -- What the stages keep of the memory before them.
  obtain toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) →
      Region.Disjoint ⟨p, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  obtain ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  obtain cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hS : ∀ j < r, blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) :=
    fun j hj => by
      obtain hk : 16 * e + j < nb s₀ := by omega_arith
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk]
      simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The ciphertext of the blocks after the last group.
  obtain hX : ∀ j < r, E.X j = ctb s₀ (16 * e + j) := fun j hj => by
    show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [hS j hj, eK, m₃, ks₂ j hj]
  -- The blocks.
  obtain hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      obtain hj : j < r := by omega_arith
      obtain ct := hI₄.ct j hj
      obtain eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct, hX j hj]
  -- The powers, as the key context holds them: kept by the stores before the loop.
  obtain kS : ∀ {d : Nat}, d + 16 ≤ 512 →
      s₃.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 = s₀.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 := fun {d} hd => by
    obtain hsub : Region.Sub ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩ ⟨kp s₀, 512⟩ := Offset.sub_base _ hd
    rw [m₃, f₂.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (hc.p_k.symm.sub_left hsub).sub_right (Offset.sub_base _ (by omega_arith))) (by decide),
      m₁, Mem.readW_writeW_sep ((hc.c_k.symm.sub_left hsub).sep (Region.contains_self _ _) cw) (by decide)]
    exact hI.a.frame.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hc.d_k.symm.sub_left hsub
      · exact hc.p_k.symm.sub_left hsub) (by decide)
  obtain hT : ∀ j < r, E.TC j = powC s₀ ((16 - r + j) / 2) ((16 - r + j) % 2) := fun j hj => by
    show s₃.mem.readW (E.aC j) 128 = _
    rw [eC j hj, kS (by omega_arith), ctxPow_at hc (by omega_arith) (by omega_arith)]
    simp only [powC]
    congr 2; omega_arith
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₇.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, blockAt_frame fz (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact ksP k hk), hb₄ k hk]
  obtain fA : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (ctb s₀)) := by
    rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show blockAt s₇.mem (cp s₀) = _
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl, blockAt_frame fz (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      blockAt_frame hI₄.frame (fA _ hp.d_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide), Nat.add_zero,
      VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₇.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₇.mem (dp s₀) (nb s₀))
    obtain hbl : blocksAt s₇.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
      simp only [blocksAt]
      exact List.map_congr_left fun k hk => hb k (by simpa using hk)
    rw [hbl, m₇, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.prod, accR_congr _ r hX hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₇.mem
    obtain F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    obtain F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    obtain F3 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    obtain F4 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₄.mem s₆.mem := fz.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    rw [m₇]
    exact ((((F0.trans F1).trans F2).trans F3).trans F4).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₇.gpr q = _
    by_cases h11 : q = .r11
    · subst h11
      rw [g₇, a11']
    · rw [g₇, g₆ q h11, f₅.gpr, hI₄.gpr q h3 h4 h1]
      show s₃.gpr q = _
      rw [gk₃ q h4 h11 h1]
      exact hI.gpr q h1 h2 h3 h4
  · show s₇.rd = _
    rw [rd₇, rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₇.wr = _
    rw [wr₇, wr₆, f₅.wr, hI₄.wr]; exact hwr₃
  · show Frame _ s.mem s₇.mem
    obtain G1 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain G2 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₁.mem s₃.mem := by
      rw [m₃]; exact f₂.mono fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; simp
    obtain G3 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₃.mem s₄.mem :=
      hI₄.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    obtain G4 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₄.mem s₆.mem :=
      fz.mono fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; simp
    rw [m₇]
    exact (((G1.trans G2).trans G3).trans G4).writeW (by simp) _ (Region.contains_self _ _)
  · intro i hi
    show s₇.mem _ = _
    rw [← hr_def]
    obtain hxP : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    obtain k7 : s₇.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) = s₆.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
      rw [m₇]
      exact ((Frame.refl [yR s₀] _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) _
        fun r' hr' hc' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hp.p_y _ hxP hc'
    rw [k7]
    by_cases hz : i < 128 ∨ 8 < r
    · simp only [hz, ↓reduceIte]
      exact zb i (by split <;> omega_arith)
    · simp only [hz, ↓reduceIte]
      obtain hr8 : r ≤ 8 := by omega_arith
      obtain nk : ∀ r' ∈ [(⟨pp s₀ + BitVec.ofNat 64 256, 128⟩ : Region)],
          ¬ r'.Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 := fun r' hr' hc' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        change (pp s₀ + BitVec.ofNat 64 (256 + i) - (pp s₀ + BitVec.ofNat 64 256)).toNat < 128 at hc'
        rw [Offset.lt_iff _ _ (by omega_arith), Mem.sub_ofNat_toNat _ (by omega_arith)] at hc'
        omega_arith
      rw [fz' hr8 _ nk, hI₄.frame _ fun r' hr' hc' => ?_, show E.m = s₃.mem from rfl, m₃, f₂' hr8 _ nk, m₁]
      · exact ((Frame.refl [cR s₀] _).writeW (List.mem_singleton_self _) _ cw) _
          fun r' hr' hc' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hp.p_c _ hxP hc'
      · simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.d_p _ (Offset.sub_base (dp s₀) (d := 16 * (16 * e)) (n := 16 * r) (k := 16 * nb s₀)
          (by omega_arith) _ hc') hxP

theorem remE_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (hc : CtxPow s₀ (dR s₀)) (hr : RemLaw (hk s₀) (powC s₀))
    {P : Nat → Nat → Block} {e : Nat}
    {s : State} (hI : EInvR s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa (remE .rdx) s (EPost s₀) :=
  WP.mono (remE_okF hp hc hr hI hlt hne) fun _ h => h.1

/-- After the decryption loop stops, `r9` raised by 16: `EInvR` with `Y`
over the blocks as read. -/
structure DInvR (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (16 + (nb s₀ - 16 * e))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : s.lane .xmm2 1 = 0

/-- Before any group, `EInvR` is `DInvR`: nothing is hashed yet. -/
theorem EInvR.toD0 {s₀ : State} {P : Nat → Nat → Block} {s : State} (h : EInvR s₀ P 0 s) : DInvR s₀ P 0 s :=
  ⟨h.a, h.rdx, h.r9, h.rax, h.gpr, h.pw, h.m1, by rw [h.y]; rfl, h.y1⟩

/-- `remD`, the decryption of the blocks after the last group, and what it
leaves at `scratch + 256`, where it puts the keystream: its first 128 bytes,
and the next 128 if `r > 8`, cleared, and nothing else written but the
counter, `Y` and the data. -/
theorem remD_okF {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (hc : CtxPow s₀ (dR s₀)) (hr : RemLaw (hk s₀) (powC s₀))
    {P : Nat → Nat → Block} {e : Nat}
    {s : State} (hI : DInvR s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa remD s fun s' => DPost s₀ s' ∧
      Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem ∧
      ∀ i < 256, s'.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) =
        if i < 128 ∨ 8 < nb s₀ - 16 * e then 0 else s.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have hle := hI.a.le
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain ⟨r, hr_def⟩ : ∃ r, r = nb s₀ - 16 * e := ⟨_, rfl⟩
  obtain hr1 : 1 ≤ r := by omega_arith
  obtain hr15 : r ≤ 15 := by omega_arith
  obtain hr9 : s.gpr .r9 = BitVec.ofNat 64 (16 + r) := by rw [hI.r9, ← hr_def]
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  rw [show remD = .seq (.block Impl.Gcm.X86_64.StitchR.remSetupC) (.seq ksSel
      (.seq (.block ((([.alu .sub .r11 (.imm 512), .mov32 .r10 (.imm 0)] : List Instr) ++
          Impl.Gcm.X86_64.StitchAvx.zero) ++ ([.alu .test .r9 (.imm 1)] : List Instr)))
        (.seq (.ite .e (.block [.alu .cmp .r9 (.imm 16)])
            (.block Impl.Gcm.X86_64.StitchR.remOneD))
          (.seq (.ite .e (.block []) (.seq (.loop (.block (Impl.Gcm.X86_64.StitchR.remPairD ++
              [.alu .sub .rax (.imm 64)] ++ Impl.Gcm.X86_64.StitchR.remNextPair)) .ne)
              (.block Impl.Gcm.X86_64.StitchR.foldLanes)))
            (.seq (.block (Impl.Gcm.X86_64.StitchAvx.reduceHash ++ ([.alu .add .r11 (.imm 512)] : List Instr)))
              (.seq Impl.Gcm.X86_64.StitchR.zeroKs (.block storeY))))))) from rfl]
  -- The counter after all the blocks, and `rax` at the powers of the `r` blocks in the key context.
  refine WP.seq (WP.mono (remSetupC_ok s hr1 hr15 hr9 (hI.a.msk 0 (by decide))
    (by rw [hI.rax, hI.a.wr]; exact in_sub_int hp.c_in (by omega_arith)))
    fun s₁ ⟨m₁, a10₁, ax₁, g₁, rd₁, wr₁, z₁⟩ => ?_)
  obtain e0 : cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int) = cp s₀ := by
    rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _
  rw [hI.rax, e0] at m₁
  rw [hI.a.rdi] at ax₁
  obtain lk₁ : ∀ x, x ≠ .xmm13 → ∀ l < 2, s₁.lane x l = s.lane x l := fun x h l hl => by
    rw [← State.zlane_lt2 _ _ hl, z₁ x h l (by omega_arith), State.zlane_lt2 _ _ hl]
  obtain cw : (cR s₀).Contains (cp s₀) (128 / 8) := Region.contains_self _ _
  obtain hfr₁ : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s₁.mem := by
    rw [m₁]
    exact (hI.a.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cw
  obtain hrd₁ : s₁.rd = s₀.rd := by rw [rd₁]; exact hI.a.rd
  obtain hwr₁ : s₁.wr = s₀.wr := by rw [wr₁]; exact hI.a.wr
  obtain hrdi₁ : s₁.gpr .rdi = kp s₀ := by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rdi
  -- The keystream.
  refine WP.seq (WP.mono (ksSel_okF hp hr1 hr15 (c := 16 * e) a10₁
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.ctr l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.msk l hl)
    (fun l hl => by rw [lk₁ _ (by decide) l hl]; exact hI.a.inc l hl)
    (keys_of hp hrdi₁ hrd₁ hwr₁ hfr₁)
    (by rw [g₁ _ (by decide) (by decide)]; exact hI.a.rsi) hrdi₁
    (by rw [g₁ _ (by decide) (by decide)]; exact hr11) hwr₁)
    fun s₂ ⟨⟨ks₂, g₂, rd₂, wr₂, l₂, f₂⟩, f₂'⟩ => ?_)
  -- `r11` lowered, `r10 = 0`, the products cleared.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preV_ok s₂) fun s₃ ⟨d₃, z₃, g₃, p₃, l₃, m₃, rd₃, wr₃⟩ => ?_
  obtain gk₃ : ∀ q, q ≠ .r10 → q ≠ .r11 → q ≠ .rax → s₃.gpr q = s.gpr q := fun q h1 h11 h2 => by
    rw [g₃ q h11 h1, g₂ q h1, g₁ q h1 h2]
  obtain lk₃ : ∀ x, x ≠ .xmm8 → x ≠ .xmm9 → x ≠ .xmm10 → x ≠ .xmm13 → x ≠ .xmm14 → x ∉ aregs →
      ∀ l < 2, s₃.lane x l = s.lane x l := fun x h8 h9 h10 h13 h14 ha l hl => by
    rw [← State.zlane_lt2 _ _ hl, l₃ x h8 h9 h10 l (by omega_arith), State.zlane_lt2 _ _ hl, l₂ x h13 h14 ha l hl,
      lk₁ x h13 l hl]
  obtain h11₃ : s₃.gpr .r11 = pp s₀ - BitVec.ofNat 64 512 := by
    rw [d₃, g₂ _ (by decide), g₁ _ (by decide) (by decide), hr11]
  obtain eK : ∀ j, pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j) =
      pp s₀ + BitVec.ofNat 64 (256 + 16 * j) := fun j => by
    rw [show 768 + 16 * j = 512 + (256 + 16 * j) by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  obtain hA : s₃.gpr .rdx = bAddr s₀ (16 * e) := by
    rw [gk₃ _ (by decide) (by decide) (by decide), hI.rdx]
    show dp s₀ + BitVec.ofNat 64 (256 * e) = dp s₀ + BitVec.ofNat 64 (16 * (16 * e))
    rw [show 256 * e = 16 * (16 * e) by omega_arith]
  let E : REnv := REnv.mk r .rdx (bAddr s₀ (16 * e)) (bAddr s₀ (16 * e)) (pp s₀ - BitVec.ofNat 64 512)
    (kp s₀ + BitVec.ofNat 64 224) s₃.mem s₃.gpr s₃.rd s₃.wr (s₃.lane .xmm2 0)
  have hwk := hc.wrap_k
  obtain eC : ∀ j, j < r → E.aC j = kp s₀ + BitVec.ofNat 64 (224 + 16 * (r - j) + 32 * ((r - j) % 2)) := fun j _ => by
    show kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - j) + 32 * ((r - j) % 2)) = _
    rw [Offset.add_add, Nat.add_assoc]
  obtain kD : ∀ {d n : Nat}, d + n ≤ 512 → Region.Disjoint ⟨kp s₀ + BitVec.ofNat 64 d, n⟩ ⟨bAddr s₀ (16 * e), 16 * r⟩ :=
    fun {d n} h => (hc.d_k.symm.sub_left (Offset.sub_base _ h)).sub_right
      (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hrd₁]
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hwr₁]
  obtain hE : OkC E :=
    { r1 := hr1, r15 := hr15, gS := hA, gA := hA, gP := h11₃
      gW := by
        show s₃.gpr .rax = _; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁]
      src9 := by show Reg.rdx ≠ Reg.r9; decide, src10 := by show Reg.rdx ≠ Reg.r10; decide
      srcA := by show Reg.rdx ≠ Reg.rax; decide
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
        rw [eC j hj, show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith)
      dS := fun j (hj : j < r) i hi => by
        show Region.Disjoint ⟨bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (16 * e), 16 * i⟩
        exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      dK := fun j (hj : j < r) => by
        show Region.Disjoint ⟨pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (16 * e), 16 * r⟩
        rw [eK]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < r) => by
        rw [eC j hj]; exact kD (by omega_arith)
      inS2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hrd₃, hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inK2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions (s₃.rd ++ s₃.wr) (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) 32
        rw [hrd₃, hwr₃, eK]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD2 := fun j (hj : j + 2 ≤ r) => by
        show InRegions s₃.wr (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) 32
        rw [hwr₃, Offset.add_add, ← Nat.mul_add]
        exact in_sub hp.d_in (by omega_arith)
      inW2 := fun j (hj : j + 2 ≤ r) (hev : (r - j) % 2 = 0) => by
        rw [eC j (by omega_arith), show E.rd ++ E.wr = s₃.rd ++ s₃.wr from rfl, hrd₃, hwr₃]
        exact in_sub hc.k_in (by omega_arith) }
  obtain hI₃ : RInvC E E.H 0 s₃ :=
    { le := Nat.zero_le _, r10 := z₃
      ax := by
        show s₃.gpr .rax + s₃.gpr .r10 = kp s₀ + BitVec.ofNat 64 224 + BitVec.ofNat 64 (16 * (r - 0))
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), ax₁, z₃, Nat.sub_zero]
        exact BitVec.add_zero _
      r9 := by
        show s₃.gpr .r9 = _
        rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hr9, Nat.sub_zero]
      gpr := fun _ _ _ _ => rfl, rd := rfl, wr := rfl
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
  obtain z1 : ∀ x, s₃.zlane x 1 = 0 → s₃.lane x 1 = 0 := fun x h => by rw [← State.zlane_lt2 _ _ (by decide)]; exact h
  -- The first block alone if `r` is odd, then the pairs and their lanes added.
  refine remMidDC_ok (E := E) hE rfl hI₃ (z1 _ (p₃ 1 (by decide)).1) (z1 _ (p₃ 1 (by decide)).2.1)
    (z1 _ (p₃ 1 (by decide)).2.2)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]; exact hI.y1)
    (by rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1 (by decide)]
        exact hI.a.msk 1 (by decide)) fun s₄ hI₄ => ?_
  -- The products reduced into `Y`, `r11` restored, the keystream cleared, and `Y` stored.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₄ hI₄.m1) fun s₅ ⟨y₅, f₅⟩ => ?_
  refine WP.mono (add11_ok s₅) fun s₅a ⟨a11, g₅a, l₅a, m₅a, rd₅a, wr₅a⟩ => ?_
  obtain h11₅a : s₅a.gpr .r11 = pp s₀ := by
    rw [a11, f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .r11 + BitVec.ofNat 64 512 = _
    rw [h11₃, BitVec.sub_add_cancel]
  obtain h10₅a : s₅a.gpr .r10 = BitVec.ofNat 64 (16 * r) := by
    rw [g₅a _ (by decide), f₅.gpr, hI₄.r10]
  obtain hin₅ : InRegions s₅a.wr (s₅a.gpr .r11) 1024 := by
    rw [h11₅a, wr₅a, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.p_in
  refine WP.seq (WP.mono (Stitch.wp_and (zeroKs_ok (r := r) hr15 h10₅a hin₅ (by rw [h11₅a]; exact hwp))
    (zeroKs_bytes (r := r) hr15 h10₅a hin₅ (by rw [h11₅a]; exact hwp)))
    fun s₆ ⟨⟨fz, zz, gz, rdz, wrz, lz⟩, fz', zb⟩ => ?_)
  rw [h11₅a] at fz zz fz' zb
  obtain g₆ : ∀ q, q ≠ .r11 → s₆.gpr q = s₅.gpr q := fun q h => by rw [gz, g₅a q h]
  obtain l₆ : ∀ x, x ≠ .xmm12 → ∀ l < 2, s₆.lane x l = s₅.lane x l := fun x h l hl => by rw [lz x h l hl, l₅a]
  obtain rd₆ : s₆.rd = s₅.rd := by rw [rdz, rd₅a]
  obtain wr₆ : s₆.wr = s₅.wr := by rw [wrz, wr₅a]
  obtain a11' : s₆.gpr .r11 = pp s₀ := by rw [gz, h11₅a]
  obtain hrcx : s₆.gpr .rcx = yp s₀ := by
    rw [g₆ _ (by decide), f₅.gpr, hI₄.gpr _ (by decide) (by decide) (by decide)]
    show s₃.gpr .rcx = _
    rw [gk₃ _ (by decide) (by decide) (by decide)]
    exact hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  obtain m06 : s₆.lane .xmm0 0 = revMask := by
    rw [l₆ _ (by decide) 0 (by decide), f₅.lane _ (by decide) 0 (by decide)]; exact hI₄.m0
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl, WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₆ m06
    (by rw [hrcx, wr₆, f₅.wr, hI₄.wr]; show InRegions s₃.wr _ _; rw [hwr₃]; exact hp.y_in))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hrcx, l₆ _ (by decide) 0 (by decide), y₅] at m₇
  obtain hm₅a : s₅a.mem = s₄.mem := by rw [m₅a, f₅.mem]
  rw [hm₅a] at fz fz'
  obtain hnb : nb s₀ = 16 * e + r := by omega_arith
  -- What the stages keep of the memory before them.
  obtain toS : ∀ p : Addr, Region.Disjoint ⟨p, 16⟩ (cR s₀) →
      Region.Disjoint ⟨p, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ →
      blockAt s₃.mem p = blockAt s.mem p := fun p hc hk => by
    rw [m₃, blockAt_frame f₂ (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hk), m₁,
      show cp s₀ = (cR s₀).base from rfl, blockAt_writeW_sep' hc rfl]
  obtain ksP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩ := fun k hk =>
    (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  obtain cP : ∀ k, k < nb s₀ → Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hS : ∀ j < r, blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) = blk s₀ (16 * e + j) :=
    fun j hj => by
      obtain hk : 16 * e + j < nb s₀ := by omega_arith
      rw [Offset.add_add, ← Nat.mul_add, toS _ (cP _ hk) (ksP _ hk), hI.a.blocks _ hk]
      simp only [show ¬ 16 * e + j < 16 * e by omega_arith, ite_false]
  -- The plaintext of the blocks after the last group.
  obtain hX : ∀ j < r, E.X j = ctb s₀ (16 * e + j) := fun j hj => by
    show blockAt s₃.mem (bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₃.mem (pp s₀ - BitVec.ofNat 64 512 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [hS j hj, eK, m₃, ks₂ j hj]
  -- The blocks.
  obtain hb₄ : ∀ k < nb s₀, blockAt s₄.mem (bAddr s₀ k) = ctb s₀ k := by
    intro k hk
    by_cases hke : k < 16 * e
    · rw [blockAt_frame hI₄.frame (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          show Region.Disjoint _ ⟨bAddr s₀ (16 * e), 16 * r⟩
          exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        toS _ (cP k hk) (ksP k hk), hI.a.blocks k hk]
      simp only [hke, ite_true]
    · obtain ⟨j, rfl⟩ : ∃ j, k = 16 * e + j := ⟨k - 16 * e, by omega_arith⟩
      obtain hj : j < r := by omega_arith
      obtain ct := hI₄.ct j hj
      obtain eD : E.aD j = bAddr s₀ (16 * e + j) := by
        show bAddr s₀ (16 * e) + BitVec.ofNat 64 (16 * j) = _
        rw [Offset.add_add, ← Nat.mul_add]
      rw [eD] at ct
      rw [ct, hX j hj]
  -- The powers, as the key context holds them: kept by the stores before the loop.
  obtain kS : ∀ {d : Nat}, d + 16 ≤ 512 →
      s₃.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 = s₀.mem.readW (kp s₀ + BitVec.ofNat 64 d) 128 := fun {d} hd => by
    obtain hsub : Region.Sub ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩ ⟨kp s₀, 512⟩ := Offset.sub_base _ hd
    rw [m₃, f₂.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (hc.p_k.symm.sub_left hsub).sub_right (Offset.sub_base _ (by omega_arith))) (by decide),
      m₁, Mem.readW_writeW_sep ((hc.c_k.symm.sub_left hsub).sep (Region.contains_self _ _) cw) (by decide)]
    exact hI.a.frame.readW (r := ⟨kp s₀ + BitVec.ofNat 64 d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hc.d_k.symm.sub_left hsub
      · exact hc.p_k.symm.sub_left hsub) (by decide)
  obtain hT : ∀ j < r, E.TC j = powC s₀ ((16 - r + j) / 2) ((16 - r + j) % 2) := fun j hj => by
    show s₃.mem.readW (E.aC j) 128 = _
    rw [eC j hj, kS (by omega_arith), ctxPow_at hc (by omega_arith) (by omega_arith)]
    simp only [powC]
    congr 2; omega_arith
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, blockAt s₇.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' (yD k hk) rfl, blockAt_frame fz (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact ksP k hk), hb₄ k hk]
  obtain fA : ∀ R : Region, R.Disjoint (dR s₀) → ∀ r' ∈ [(⟨E.A, 16 * E.r⟩ : Region)], R.Disjoint r' :=
    fun R hR r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hR.sub_right (Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith))
  obtain hH : ∀ j < r, E.H j = blk s₀ (16 * e + j) := fun j hj => hS j hj
  obtain hy₃ : s₃.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀)) := by
    rw [lk₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 (by decide)]
    exact hI.y
  refine ⟨⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show blockAt s₇.mem (cp s₀) = _
    rw [m₇, show yp s₀ = (yR s₀).base from rfl, blockAt_writeW_sep' hp.c_y rfl, blockAt_frame fz (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      blockAt_frame hI₄.frame (fA _ hp.d_c.symm), show E.m = s₃.mem from rfl, m₃,
      blockAt_frame f₂ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.p_c.symm.sub_right (Offset.sub_base _ (by omega_arith))),
      m₁, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide), Nat.add_zero,
      VG.Proof.Aes.X86_64.AesNi.rep_add, hnb]
  · show blockAt s₇.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
    have hbl : blocksAt s₀.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (blk s₀) := rfl
    rw [hbl, m₇, VG.Proof.Gcm.X86_64.blockAt_store, hI₄.prod, accR_congr _ r hH hT, hr r hr1 hr15,
      show E.y = s₃.lane .xmm2 0 from rfl, hy₃, hnb, List.range_add, List.map_append, List.map_map]
    simp only [ghashFrom, List.foldl_append]
    rfl
  · show Frame _ s₀.mem s₇.mem
    obtain F0 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem := hI.a.frame.sub fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    obtain F1 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain F2 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₁.mem s₃.mem := by
      rw [m₃]
      exact f₂.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    obtain F3 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₃.mem s₄.mem := hI₄.frame.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    obtain F4 : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₄.mem s₆.mem := fz.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩
    rw [m₇]
    exact ((((F0.trans F1).trans F2).trans F3).trans F4).writeW (by simp) _ (Region.contains_self _ _)
  · intro q h1 h2 h3 h4
    show s₇.gpr q = _
    by_cases h11 : q = .r11
    · subst h11
      rw [g₇, a11']
    · rw [g₇, g₆ q h11, f₅.gpr, hI₄.gpr q h3 h4 h1]
      show s₃.gpr q = _
      rw [gk₃ q h4 h11 h1]
      exact hI.gpr q h1 h2 h3 h4
  · show s₇.rd = _
    rw [rd₇, rd₆, f₅.rd, hI₄.rd]; exact hrd₃
  · show s₇.wr = _
    rw [wr₇, wr₆, f₅.wr, hI₄.wr]; exact hwr₃
  · show Frame _ s.mem s₇.mem
    obtain G1 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (by simp) _ cw
    obtain G2 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₁.mem s₃.mem := by
      rw [m₃]; exact f₂.mono fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; simp
    obtain G3 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₃.mem s₄.mem :=
      hI₄.frame.sub fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact ⟨dR s₀, by simp, Offset.sub_base _ (by show 16 * (16 * e) + 16 * r ≤ 16 * nb s₀; omega_arith)⟩
    obtain G4 : Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s₄.mem s₆.mem :=
      fz.mono fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; simp
    rw [m₇]
    exact (((G1.trans G2).trans G3).trans G4).writeW (by simp) _ (Region.contains_self _ _)
  · intro i hi
    show s₇.mem _ = _
    rw [← hr_def]
    obtain hxP : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    obtain k7 : s₇.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) = s₆.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
      rw [m₇]
      exact ((Frame.refl [yR s₀] _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) _
        fun r' hr' hc' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hp.p_y _ hxP hc'
    rw [k7]
    by_cases hz : i < 128 ∨ 8 < r
    · simp only [hz, ↓reduceIte]
      exact zb i (by split <;> omega_arith)
    · simp only [hz, ↓reduceIte]
      obtain hr8 : r ≤ 8 := by omega_arith
      obtain nk : ∀ r' ∈ [(⟨pp s₀ + BitVec.ofNat 64 256, 128⟩ : Region)],
          ¬ r'.Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 := fun r' hr' hc' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        change (pp s₀ + BitVec.ofNat 64 (256 + i) - (pp s₀ + BitVec.ofNat 64 256)).toNat < 128 at hc'
        rw [Offset.lt_iff _ _ (by omega_arith), Mem.sub_ofNat_toNat _ (by omega_arith)] at hc'
        omega_arith
      rw [fz' hr8 _ nk, hI₄.frame _ fun r' hr' hc' => ?_, show E.m = s₃.mem from rfl, m₃, f₂' hr8 _ nk, m₁]
      · exact ((Frame.refl [cR s₀] _).writeW (List.mem_singleton_self _) _ cw) _
          fun r' hr' hc' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hp.p_c _ hxP hc'
      · simp only [List.mem_singleton] at hr'; subst hr'
        exact hp.d_p _ (Offset.sub_base (dp s₀) (d := 16 * (16 * e)) (n := 16 * r) (k := 16 * nb s₀)
          (by omega_arith) _ hc') hxP

theorem remD_ok {s₀ : State} {lo : Nat} (hp : SPre s₀ lo) (hc : CtxPow s₀ (dR s₀)) (hr : RemLaw (hk s₀) (powC s₀))
    {P : Nat → Nat → Block} {e : Nat}
    {s : State} (hI : DInvR s₀ P e s) (hlt : nb s₀ - 16 * e < 16) (hne : nb s₀ ≠ 16 * e) :
    WP isa remD s (DPost s₀) :=
  WP.mono (remD_okF hp hc hr hI hlt hne) fun _ h => h.1

/-- `add r9, 16` after the decryption loop. -/
theorem add9D_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : DInv s₀ P e s) :
    WP isa (.block [.alu .add .r9 (.imm 16)]) s fun s' => DInvR s₀ P e s' ∧ s'.mem = s.mem := by
  have hle := hI.a.le
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.mono (StitchZH.add9_ok s) fun s' ⟨a9, ga, la, ma, rda, wra⟩ => ⟨?_, ma⟩
  obtain la' : ∀ x l, l < 2 → s'.lane x l = s.lane x l := fun x l hl => by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, la]
  exact
    { a := ⟨hI.a.le, fun l hl => by rw [la' _ _ hl]; exact hI.a.ctr l hl, fun l hl => by rw [la' _ _ hl]; exact hI.a.msk l hl,
        fun l hl => by rw [la' _ _ hl]; exact hI.a.inc l hl, by rw [ga _ (by decide)]; exact hI.a.rdi,
        by rw [ga _ (by decide)]; exact hI.a.rsi, by rw [ga _ (by decide)]; exact hI.a.r10,
        by rw [ma]; exact hI.a.frame, fun k hk => by rw [ma]; exact hI.a.blocks k hk, by rw [rda]; exact hI.a.rd,
        by rw [wra]; exact hI.a.wr⟩
      rdx := by rw [ga _ (by decide)]; exact hI.rdx
      r9 := by
        rw [a9, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
        congr 1; omega_arith
      rax := by rw [ga _ (by decide)]; exact hI.rax
      gpr := fun r h1 h2 h3 h4 => by rw [ga r h3]; exact hI.gpr r h1 h2 h3 h4
      pw := fun k hk l hl => by rw [ma]; exact hI.pw k hk l hl
      m1 := fun l hl => by rw [la' _ _ hl]; exact hI.m1 l hl
      y := by rw [la' _ _ (by decide)]; exact hI.y
      y1 := by rw [la' _ _ (by decide)]; exact hI.y1 }

/-- The end of `decR` once its loop has stopped with `r` blocks left: with
none, the counter and `Y` stored; otherwise `r9` raised by 16 and `remD`, and
what it writes. -/
theorem dtailR_okF {s₀ : State} (hp : SPre s₀) (hc : CtxPow s₀ (dR s₀)) (hr : RemLaw (hk s₀) (powC s₀))
    {P : Nat → Nat → Block} {e : Nat} {s : State} (hlt : nb s₀ - 16 * e < 16) (hI : DInv s₀ P e s) :
    WP isa Impl.Gcm.X86_64.StitchR.tailD s fun s' =>
      DPost s₀ s' ∧ Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem ∧
      ∀ i < 256, s'.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) =
        if nb s₀ ≠ 16 * e ∧ (i < 128 ∨ 8 < nb s₀ - 16 * e) then 0 else s.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hwp := hp.wrap_p
  have hle := hI.a.le
  unfold Impl.Gcm.X86_64.StitchR.tailD
  refine WP.seq (WP.mono (StitchZH.test99_ok s) fun s₆ ⟨z₆, g₆, l₆, m₆, rd₆, wr₆⟩ => ?_)
  obtain yf : YFrame [] s s₆ :=
    ⟨g₆, m₆, rd₆, wr₆, fun x _ l hl => by rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, l₆]⟩
  obtain hI₆ : DInv s₀ P e s₆ :=
    ⟨hI.a.yframe yf (by simp) (by simp) (by simp), by rw [g₆]; exact hI.rdx, by rw [g₆]; exact hI.r9,
      by rw [g₆]; exact hI.rax, fun r h1 h2 h3 h4 => by rw [g₆]; exact hI.gpr r h1 h2 h3 h4,
      fun k hk l hl => by rw [m₆]; exact hI.pw k hk l hl, fun l hl => by rw [yf.lane _ (by simp) l hl]; exact hI.m1 l hl,
      by rw [yf.lane _ (by simp) 0 (by decide)]; exact hI.y, by rw [yf.lane _ (by simp) 1 (by decide)]; exact hI.y1⟩
  obtain hz : (s.gpr .r9 &&& s.gpr .r9 == 0) = decide (nb s₀ = 16 * e) := by
    rw [BitVec.and_self, hI.r9]
    by_cases h : nb s₀ = 16 * e
    · rw [show nb s₀ - 16 * e = 0 by omega_arith, decide_eq_true h]; rfl
    · have : BitVec.ofNat 64 (nb s₀ - 16 * e) ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_arith
      rw [beq_false_of_ne this, decide_eq_false h]
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₆, hz]) (fun h => ?_) (fun h => ?_)
  · have he : nb s₀ = 16 * e := by simpa using h
    refine WP.mono (Stitch.dfinalM_okF hp.toM he hI₆.toM) fun s' ⟨h', f'⟩ => ⟨h'.toDPost, ?_, fun i hi => ?_⟩
    · rw [m₆] at f'
      exact f'.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [he, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [f' _ fun r hr hc' => ?_, m₆]
      obtain hxP : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 :=
        Offset.contains_base _ (by omega_arith) (by omega_arith)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.p_c _ hxP hc'
      · exact hp.p_y _ hxP hc'
  · have hne : nb s₀ ≠ 16 * e := by simpa using h
    refine WP.seq (WP.mono (add9D_ok hI₆) fun s₇ ⟨hI₇, m₇⟩ => ?_)
    refine WP.mono (remD_okF hp hc hr hI₇ hlt hne) fun s' ⟨h', f', b'⟩ =>
      ⟨h', by rw [m₇, m₆] at f'; exact f', fun i hi => ?_⟩
    simp only [ne_eq, hne, not_false_eq_true, true_and]
    rw [b' i hi, m₇, m₆]

/-- `loopER_ok`, and what the loop writes: the data. -/
theorem loopER_okF {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' =>
      (∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e s') ∧ Frame [dR s₀] s.mem s'.mem := by
  obtain fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → Frame [dR s₀] s.mem t.mem →
      (∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e t) ∧ Frame [dR s₀] s.mem t.mem :=
    fun e he t hI hF => ⟨⟨e, he, hI⟩, hF⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI (Frame.refl _ _))
  · let I : Nat → State → Prop := fun m t => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e t ∧
      Frame [dR s₀] s.mem t.mem
    obtain hstep : ∀ m t, I m t → WP isa body t (fun s' =>
        (eval .ae s' = some false ∧ ((∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e s') ∧ Frame [dR s₀] s.mem s'.mem)) ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m t ⟨e, rfl, he, hI, hF⟩
      refine WP.mono (Stitch.body_okF hp hf he hI) fun s' ⟨⟨hI', hcf'⟩, hF'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI' (hF.trans hF')⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI', hF.trans hF'⟩
    have := hI.a.le
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega_arith, hI, Frame.refl _ _⟩

/-- The encryption loop, for any number of blocks from 16 on: it stops with
`16 + r` blocks left, `r < 16`. -/
theorem loopER_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' =>
      ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e s' := by
  obtain fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ - 16 * (e - 1) < 32 ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, he, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e s
    obtain hstep : ∀ m s, I m s → WP isa body s (fun s' =>
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
theorem cmpE16_okF {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s)
    (hlt : nb s₀ - 16 * (e - 1) < 32) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      (EInv s₀ P e s' ∧ s'.zf = some (decide (nb s₀ = 16 * e))) ∧ s'.mem = s.mem := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.mono (cmp916_ok s) fun s' ⟨z, g, l, m, rd, wr⟩ => ⟨⟨?_, ?_⟩, m⟩
  · have yf : YFrame [] s s' := ⟨g, m, rd, wr, fun x _ l' hl => l x l'⟩
    exact ⟨hI.a.yframe yf (by simp) (by simp) (by simp), hI.one, by rw [g]; exact hI.rdx, by rw [g]; exact hI.r9,
      by rw [g]; exact hI.rax, fun r h1 h2 h3 h4 => by rw [g]; exact hI.gpr r h1 h2 h3 h4,
      fun k hk l' hl => by rw [m]; exact hI.pw k hk l' hl, fun l' hl => by rw [l]; exact hI.m1 l' hl,
      by rw [l]; exact hI.y, by rw [l]; exact hI.y1⟩
  · rw [z, hI.r9, show nb s₀ - 16 * (e - 1) = 16 + (nb s₀ - 16 * e) by omega_arith, zero16 _ (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩

theorem cmpE16_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s)
    (hlt : nb s₀ - 16 * (e - 1) < 32) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.zf = some (decide (nb s₀ = 16 * e)) :=
  WP.mono (cmpE16_okF hI hlt) fun _ h => h.1

/-- `tailE`, and what it leaves at `scratch + 256`: `remE`'s keystream
cleared, if there were blocks after the last group. -/
theorem tailER_okF {s₀ : State} (hp : SPre s₀) (hc : CtxPow s₀ (dR s₀)) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) (hr : RemLaw (hk s₀) (powC s₀)) {e : Nat} {s : State} (hlt : nb s₀ - 16 * (e - 1) < 32) (hI : EInv s₀ P e s) :
    WP isa (tailE [] .rdx) s fun s' => EPost s₀ s' ∧
      Frame [cR s₀, yR s₀, dR s₀, ⟨pp s₀ + BitVec.ofNat 64 256, 256⟩] s.mem s'.mem ∧
      ∀ i < 256, s'.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) =
        if nb s₀ ≠ 16 * e ∧ (i < 128 ∨ 8 < nb s₀ - 16 * e) then 0 else s.mem (pp s₀ + BitVec.ofNat 64 (256 + i)) := by
  have h1 := hI.one
  have hle := hI.a.le
  have hwp := hp.wrap_p
  refine WP.seq (WP.mono (cmpE16_okF hI hlt) fun s₁ ⟨⟨hI₁, z₁⟩, m₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_)
  · have he : nb s₀ = 16 * e := by simpa using h
    refine WP.mono (Stitch.final_okF hp hf he hI₁) fun s' ⟨h', f'⟩ => ⟨h', ?_, fun i hi => ?_⟩
    · rw [m₁] at f'
      exact f'.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [he, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [f' _ fun r hr hc' => ?_, m₁]
      obtain hxP : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 (256 + i)) 1 :=
        Offset.contains_base _ (by omega_arith) (by omega_arith)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.p_c _ hxP hc'
      · exact hp.p_y _ hxP hc'
  · have hne : nb s₀ ≠ 16 * e := by simpa using h
    rw [List.append_nil]
    refine WP.seq (WP.mono (lastGR_okF hp hf (by omega_arith) hI₁) fun s₂ ⟨hI₂, m₂⟩ => ?_)
    refine WP.mono (remE_okF hp hc hr hI₂ (by omega_arith) hne) fun s' ⟨h', f', b'⟩ =>
      ⟨h', by rw [m₂, m₁] at f'; exact f', fun i hi => ?_⟩
    simp only [ne_eq, hne, not_false_eq_true, true_and]
    rw [b' i hi, m₂, m₁]

/-- `tailE`, in place, once the loop has stopped. -/
theorem tailER_ok {s₀ : State} (hp : SPre s₀) (hc : CtxPow s₀ (dR s₀)) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) (hr : RemLaw (hk s₀) (powC s₀)) {e : Nat} {s : State} (hlt : nb s₀ - 16 * (e - 1) < 32) (hI : EInv s₀ P e s) :
    WP isa (tailE [] .rdx) s (EPost s₀) := by
  have h1 := hI.one
  have hle := hI.a.le
  refine WP.seq (WP.mono (cmpE16_ok hI hlt) fun s₁ ⟨hI₁, z₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ = 16 * e)) (by simp only [eval, z₁]) (fun h => ?_) (fun h => ?_)
  · exact final_ok hp hf (by simpa using h) hI₁
  · have hne : nb s₀ ≠ 16 * e := by simpa using h
    rw [List.append_nil]
    exact WP.seq (WP.mono (lastGR_ok hp hf (by omega_arith) hI₁) fun s₂ hI₂ =>
      remE_ok hp hc hr hI₂ (by omega_arith) hne)

/-- `encR` after the setup, for any number of blocks from 16 on. -/
theorem encTailR_ok {s₀ : State} (hp : SPre s₀) (hc : CtxPow s₀ (dR s₀)) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) (hr : RemLaw (hk s₀) (powC s₀)) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (tailE [] .rdx)))) s (EPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopER_ok hp hf hI₃ hcf) fun s₄ ⟨e, hlt, hI₄⟩ => tailER_ok hp hc hf hr hlt hI₄)

end VG.Proof.Gcm.X86_64.StitchR
