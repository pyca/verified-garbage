module

public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds

/-! ### `Gcm.X86_64.StitchZTo.Aes`, which this module and modules that import it used -/

section

/-!
# The out-of-place AVX-512 loop: a batch of sixteen blocks

`batchTo_ok`: `StitchZTo.batchTo j g` encrypts the sixteen plaintext blocks
at `rdx + r8 + 64 j` (blocks `c … c + 15`, `r8` holding `src - dst`) into
the output blocks at `rdx + 64 j` (`AInvTo`): the counter blocks and the
rounds as in place (`VaesZ.ctrsZ_ok`, `VaesZ.aesZ_ok`), then the XOR of the
plaintext, which nothing writes, into the output (`StitchZ.batchM_ok`, reading at `rdx + r8`), as
`StitchZ.batch_ok` does in place.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZTo (batchTo)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok aesZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the four counters, the mask, the
increment, the key schedule and its last round key, `src - dst` in `r8`,
nothing written but the output and the working space, and output blocks
below `c` the ciphertext of the plaintext's. -/
structure AInvTo (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  inc : ∀ l < 4, s.zlane .xmm15 l = four
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = sp s₀ - op s₀
  frame : Frame [oR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < c, blockAt s.mem (oAddr s₀ k) = ctbT s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInvTo.zframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvTo s₀ c s)
    (f : ZFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInvTo s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.zlane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.zlane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-- The encryption state kept by changes of `rdx` and `r9` alone. -/
theorem AInvTo.gpr2 {s₀ : State} {c : Nat} {s s' : State} (h : AInvTo s₀ c s)
    (hg : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) (hl : ∀ r l, s'.zlane r l = s.zlane r l)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AInvTo s₀ c s' :=
  ⟨h.le, fun l hl' => by rw [hl]; exact h.ctr l hl', fun l hl' => by rw [hl]; exact h.msk l hl',
    fun l hl' => by rw [hl]; exact h.inc l hl',
    by rw [hg _ (by decide) (by decide)]; exact h.rdi, by rw [hg _ (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide)]; exact h.r10, by rw [hg _ (by decide) (by decide)]; exact h.r8,
    by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.blocks k hk, by rw [hrd]; exact h.rd,
    by rw [hwr]; exact h.wr⟩

theorem AInvTo.keys {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi]; exact (sch_frame hp.toD hI.frame).symm, by rcases hp.rounds with h | h | h <;> omega_using [h],
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.toD.k_in (by rcases hp.rounds with h | h | h <;> omega_using [hj, h])⟩

/-- The plaintext is kept. -/
theorem AInvTo.src {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s)
    {k : Nat} (hk : k < nb s₀) : blockAt s.mem (sAddr s₀ k) = pblk s₀ k := by
  have hw := hp.wrap_s
  exact blockAt_frame hI.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_o.sub_left (Offset.sub_base _ (by omega_using [hk]))
    · exact hp.s_p.sub_left (Offset.sub_base _ (by omega_using [hk]))

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

/-- The same, as `StitchZ.AInvM` with the output at `r10`. -/
theorem AInvTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (h : AInvTo s₀ c s) :
    StitchZ.AInvM true s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, h.frame, h.blocks, fun _ hk _ => h.src hp hk, h.rd, h.wr⟩

theorem _root_.VG.Proof.Gcm.X86_64.StitchZ.AInvM.toTo {s₀ : State} {c : Nat} {s s' : State}
    (h : StitchZ.AInvM true s₀ c s) (hg : s.gpr = s'.gpr) (hr8 : s'.gpr .r8 = sp s₀ - op s₀) : AInvTo s₀ c s :=
  ⟨h.le, h.ctr, h.msk, h.inc, h.rdi, h.rsi, h.r10, by rw [hg]; exact hr8, h.frame, h.out, h.rd, h.wr⟩

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem :=
  WP.mono (StitchZ.batchM_ok (ix := true) (ld := true) hp.toM rfl (fun _ => rfl) g G hG Q hg hq hqx hc (hI.toM hp)
    (fun _ => hI.r8) hrdx hQ) fun _ ⟨hA, h⟩ => ⟨hA.toTo h.2.1 hI.r8, h⟩

end VG.Proof.Gcm.X86_64.StitchZTo

end

end

/-!
# The out-of-place AVX-512 loop: the setup, the loop of one group, the stores

As `StitchZ/Loop.lean` does in place. `setupCTo_ok`: the end of the setup
loads `Y` and makes the counters and the increment as `Stitch.setupC`, and
leaves `src - dst` in `r8` and `dst` in `rdx`; with the powers stored before
it (`setupTTo_ok`, `Ready2To`) and the four lanes after it (`setupZTo_ok`),
the state the loop starts from (`ReadyTo`).

`EInvTo s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInvTo`),
the ciphertext of the first `e - 1` hashed into `Y`; `rdx` points to output
group `e - 1`, the next to hash. The loop is the in-place one, out of place,
and so are its proofs: `bodyTo_ok`, `firstTo_ok` and `finalTo_ok` are
`StitchZ.bodyM_ok` and its neighbours for the output at `r10`
(`EInvTo.toM`, `EPostM.toEPostTo`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo EPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  storesK_ok pregs_get blockAt_outP)
open VG.Proof.Gcm.X86_64.StitchZ (GEnv QG gRegs gRegs_ok gq_ok QG.data keepP nextE_ok FinOk ghRun_ok ghFin
  store16Z_ok State.zlane_setV256 paddd_two_two lane0_zlane lane1_zlane shuf44_0 shuf44_1 shuf44_2 shuf44_3)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (gq setupZ lastG)
open VG.Impl.Gcm.X86_64.StitchZTo (setupCTo firstTo bodyTo)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## The setup -/

theorem setupCTo_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupCTo) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r10 ∧ s'.gpr .r8 = s.gpr .r8 - s.gpr .r10 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupCTo, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, trivial, fun r h1 h2 h3 h4 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3, h4]
  · rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

/-- After the powers are stored and `setupCTo`: the two lanes. -/
structure Ready2To (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 l (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = sp s₀ - op s₀
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : Frame [pR s₀] s₀.mem s.mem
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The setup after the powers: they are stored in the working space, then
`Y`, the counter, the increment and the pointers. -/
theorem setupTTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {s₁ : State}
    (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask) (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly)
    (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupCTo)) s₁ (Ready2To s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega_arith))
    (by rw [hr11]; simp [pregs]; omega_arith)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  have hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  refine WP.mono (setupCTo_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, r8, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨fun l hl => ?_, fun l hl => ?_, c15,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1,
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [r10, gs _ (by decide), gs _ (by decide)],
    by rw [r8, gs _ (by decide), gs _ (by decide)],
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [gk r h1 h2 h3 h4, gs r h1], by rw [m₃]; exact fr, fun k hk l hl => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

/-- The state the loop starts from. -/
structure ReadyTo (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvTo s₀ 0 s
  rdx : s.gpr .rdx = op s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The four lanes, from the two (as `StitchZ.setupZ_ok`). -/
theorem setupZTo_ok {s₀ : State} {P : Nat → Nat → Block} {s : State} (hR : Ready2To s₀ P s) :
    WP isa (.block setupZ) s (ReadyTo s₀ fun k l => P (2 * k + l / 2) (l % 2)) := by
  refine WP.mono (WP.zframe (is := setupZ) (rs := [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm1, .xmm2]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l (cb s₀)) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ (∀ l < 4, s'.zlane .xmm1 l = poly) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun s' ⟨⟨c14, m0, i15, p1, y0, y1⟩, f⟩ => ?_
  · have c0 : s.xmm .xmm14 = Nat.repeat inc32 0 (cb s₀) := by
      have h := hR.ctr 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 (cb s₀) := by
      have h := hR.ctr 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.inc 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.inc 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have m0 : s.xmm .xmm0 = revMask := by
      have h := hR.msk 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have m1 : s.ymmHi .xmm0 = revMask := by
      have h := hR.msk 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have p0 : s.xmm .xmm1 = poly := by
      have h := hR.m1 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have p1 : s.ymmHi .xmm1 = poly := by
      have h := hR.m1 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    rw [setupZ]
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl => ?_, ?_, fun l hl1 hl4 => ?_⟩⟩
    all_goals simp only [VOp.exec]
    all_goals try rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    all_goals try omega_arith
    all_goals simp (disch := decide) only [lane0_zlane, lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4,
      State.zlane_setV256, State.zlane_setV128, shuf44_0, shuf44_1, shuf44_2, shuf44_3, reduceCtorEq,
      ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
    all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
      show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
    all_goals first
      | exact c0 | exact c1 | exact m0 | exact m1 | exact p0 | exact p1
      | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [i0]; exact paddd_two_two) | (rw [i1]; exact paddd_two_two)
  · refine ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.zero_add], m0, i15, by rw [f.gpr]; exact hR.rdi,
      by rw [f.gpr]; exact hR.rsi, by rw [f.gpr]; exact hR.r10, by rw [f.gpr]; exact hR.r8,
      by rw [f.mem]; exact hR.frame.mono fun r hr => by simp at hr ⊢; exact Or.inr hr,
      fun k hk => absurd hk (Nat.not_lt_zero _), by rw [f.rd]; exact hR.rd, by rw [f.wr]; exact hR.wr⟩,
      by rw [f.gpr]; exact hR.rdx, by rw [f.gpr]; exact hR.rax,
      fun r h1 h2 h3 h4 => by rw [f.gpr]; exact hR.gpr r h1 h2 h3 h4,
      fun k hk l hl => ?_, p1, by rw [y0]; exact hR.y, y1⟩
    rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega_arith]
    exact hR.pw _ (by omega_arith) _ (by omega_arith)

/-! ## The loop of one group -/

structure EInvTo (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvTo s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (op s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 4, s.zlane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctbT s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-! ## As the in-place loop's, out of place -/

theorem EInvTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {e : Nat} {s : State}
    (h : EInvTo s₀ P e s) : StitchZ.EInvM true s₀ P e s :=
  ⟨h.a.toM hp, h.one, h.rdx, h.r9, h.rax, fun _ => h.a.r8, fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (h3 rfl) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

theorem _root_.VG.Proof.Gcm.X86_64.StitchZ.EInvM.toTo {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State}
    (h : StitchZ.EInvM true s₀ P e s) : EInvTo s₀ P e s :=
  ⟨h.a.toTo rfl (h.r8 rfl), h.one, h.rdx, h.r9, h.rax, fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (fun _ => h3) h4 h5,
    h.pw, h.m1, h.y, h.y1⟩

theorem ReadyTo.toM {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (h : ReadyTo s₀ P s) : StitchZ.ReadyM true s₀ P s :=
  ⟨h.a.toM hp, h.rdx, fun _ => h.a.r8, h.rax, fun r h1 h2 h3 h4 => h.gpr r h1 h2 (h3 rfl) h4, h.pw, h.m1, h.y, h.y1⟩

theorem bodyTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa bodyTo s fun s' => EInvTo s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) :=
  WP.mono (StitchZ.bodyM_ok hp.toM hf he (hI.toM hp)) fun _ ⟨h, hc⟩ => ⟨h.toTo, hc⟩

/-- The first group, with nothing between its rounds. -/
theorem firstTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {s : State}
    (hR : ReadyTo s₀ P s) : WP isa firstTo s (EInvTo s₀ P 1) :=
  WP.mono (StitchZ.firstM_ok hp.toM hp.nb16 (hR.toM hp)) fun _ h => h.toTo

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInvTo s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

/-! ## The stores -/

/-- The output, after all of it is encrypted. -/
theorem blocks_ctr32To {s₀ : State} {m : Mem} (hb : ∀ k < nb s₀, blockAt m (oAddr s₀ k) = ctbT s₀ k) :
    blocksAt m (op s₀) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (sp s₀) (nb s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nb s₀ := by simpa [blocksAt] using h₁
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
      List.getElem_zipWith, List.length_map, List.length_range]
    exact hb k hk

theorem _root_.VG.Proof.Gcm.X86_64.Stitch.EPostM.toEPostTo {s₀ s : State} (h : Stitch.EPostM true s₀ s) :
    EPostTo s₀ s :=
  ⟨blocks_ctr32To h.data, h.ctr, by rw [h.y]; exact congrArg _ h.blocks.symm, h.frame,
    fun r h1 h2 h3 h4 h5 => h.gpr r h1 h2 (fun _ => h3) h4 h5, h.rd, h.wr⟩

theorem finalTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : EInvTo s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPostTo s₀) :=
  WP.mono (StitchZ.finalM_ok hp.toM hf he (hI.toM hp)) fun _ h => h.toEPostTo

end VG.Proof.Gcm.X86_64.StitchZTo
