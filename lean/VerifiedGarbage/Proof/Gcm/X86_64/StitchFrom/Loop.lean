module

-- separate module: the loop's proof, which needs none of the variants' instances (`Instances.lean`), so that a change to them does not rebuild it

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchFrom
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecFrom
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt

/-!
# The out-of-place VAES decryption loop

Untrusted: everything here is checked by Lean. As `Stitch/Dec.lean` does in
place, with the roles of the addresses of `StitchTo` exchanged: `rdx` points
at the ciphertext, which both the GHASH loads and the XOR read and nothing
writes, and `r8` holds `dst - src`.

`xorDataKFrom_ok`: `xorDataKFrom t base idx regs j` XORs the lanes of the
registers into the blocks loaded from `base + 32 (j + i)` and stores them to
`base + idx + 32 (j + i)`. `batchFrom_ok`: `batchFrom j g` decrypts the
eight ciphertext blocks at `rdx + 32 j` (blocks `c … c + 7`) into the output
blocks at `rdx + r8 + 32 j` (`AInvFrom`): the counter blocks and the rounds
as in place, then `xorDataKFrom_ok`.

`setupCFrom_ok`: the end of the setup loads `Y` and makes the counter pair
and the increment as `Stitch.setupC`, and leaves `src` in `rdx` and
`dst - src` in `r8`; with the powers stored before it, the state the loop
starts from (`setupTFrom_ok`, `ReadyFrom`). `DInvFrom s₀ P e s`: `e` groups
are decrypted and the ciphertext of the first `e` hashed into `Y`; `rdx`
points to ciphertext group `e`. `dbodyFrom_ok`: a body hashes group `e`
while it decrypts it, the ciphertext read by both, which the stores to the
output keep (`QG.keepFrom`). `dfinalFrom_ok`: the stores after the loop, and
the contract (`DPostTo`).

`decR_okN`: the whole loop, for a prepared key context, given that the
powers it loads give the products of a decryption body (`PowFinD`), which
`Stitch.finD` proves where the field is imported (`AesGcm/X86_64/Instances.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchFrom


open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchFrom (xorDataKFrom)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx blockAt_writeW_out)
open VG.Proof.Gcm.X86_64.StitchTo (blockAt_writeW_lane2 load256_lane ymm_lane2)
open VG.Proof.Aes.X86_64.AesNi (ofInt_natCast blockAt_frame eval_pxor)
open VG.Proof.Gcm.X86_64 (blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- XOR the two lanes of `b` into the blocks at `base + d` and the next, and
store them to `base + idx + d` and the next. -/
theorem xor1KFrom_ok (t : XReg) (base idx : Reg) (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ t)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofInt 64 (d : Int)) 32)
    (hin : InRegions s.wr (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 t (at_ base d), .vop (.vbin .vpxor .l256 b b t),
        .vmovdquStore .l256 (atIx base idx d) b]) s fun s' =>
      (∃ v : BitVec 256, s'.mem = s.mem.writeW (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)) v) ∧
      (∀ l < 2, blockAt s'.mem (s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr base + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.lane b l) revMask) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ t → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let a := s.gpr base + s.gpr idx + BitVec.ofInt 64 (d : Int)
  let as := s.gpr base + BitVec.ofInt 64 (d : Int)
  let v := s.mem.readW as 256
  let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := (VOp.vbin .vpxor .l256 b b t).exec s₁
  have l₁ : ∀ l < 2, s₁.lane t l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₁, State.lane_setV256, v]
  rw [WP.block_cons_iff]
  refine ⟨s₁, by
    simp only [isa, exec, State.load256, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdquStore .l256 (atIx base idx d) b) s₂ =
      some (s₂.setMem (s.mem.writeW a (s₂.ymm b))) := by
    simp only [isa, exec, State.store256_eq, ea_atIx, s₂, s₁, VOp.exec_gpr,
      State.setV_gpr, VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hin, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 2, s₂.lane b l = s.lane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, lane_vbin256, ite_true, VBinOp.sse, ← l₁ l hl]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [s₁, State.lane_setV256, hb8, eval_pxor]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [blockAt_writeW_lane2 _ _ _ hl, ymm_lane2 _ _ hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq]
  · simp [s₂, s₁, lane_vbin256, State.lane_setV256, h1, h2]

theorem xorDataKFrom_ok (t : XReg) (base idx : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : t ∉ regs) (S D : Region) (hSD : S.Disjoint D)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr base + s.gpr idx + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hS : ∀ k < regs.length, ∀ l < 2,
      Region.Sub ⟨s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l)), 16⟩ S)
    (hD : Region.Sub ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩ D)
    (hw : (s.gpr base + s.gpr idx).toNat + 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorDataKFrom t base idx regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        blockAt s'.mem (s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) =
          blockAt s.mem (s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l))) ^^^
            XBinOp.eval .pshufb (s.lane regs[k] l) revMask) ∧
      Frame [⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ t → r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ t := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : t ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hinS hin hS hD hw
    rw [xorDataKFrom, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    have hinS0 := hinS 0 (by omega)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1KFrom_ok t base idx b (32 * j) s hb8 hinS0 hin0) fun s₁ ⟨⟨v, m₁⟩, b₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hD₁ : Region.Sub ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ D :=
      fun a ha => hD a (Offset.sub _ (by omega) (by omega) a ha)
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hinS (k + 1) (by omega))
      (fun k hk => by
        rw [wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (fun k hk l hl => by
        rw [g₁, show j + 1 + k = j + (k + 1) by omega]; exact hS (k + 1) (by omega) l hl)
      (by rw [g₁]; exact hD₁) (by rw [g₁]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [g₁] at hb hf
    rw [ofInt_natCast] at m₁ b₁
    have adr : ∀ (p : Addr), ∀ l < 2, p + BitVec.ofNat 64 (16 * (2 * j + l)) =
        p + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) := fun p l _ => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * j + 16 * l = 16 * (2 * j + l) by omega]
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (16 * (2 * j + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    -- The write of the first register is in `D`, apart from the ciphertext blocks still to read.
    have hW : ∀ k < bs.length + 1, ∀ l < 2, Region.Disjoint
        ⟨s.gpr base + BitVec.ofNat 64 (16 * (2 * (j + k) + l)), 16⟩
        ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * j), 32⟩ := fun k hk l hl =>
      (hSD.sub_left (hS k hk l hl)).sub_right fun a ha => hD a (Region.sub_prefix (by omega) a ha)
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), adr _ l hl, b₁ l hl, adr _ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, m₁,
          blockAt_writeW_out (R := ⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * j), 32⟩) (by
            rw [show j + 1 + k = j + (k + 1) by omega]; exact hW (k + 1) (by omega) l hl) rfl,
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk')) l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr base + s.gpr idx + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.sub _ (by omega) (by omega) a ha
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2 l hl, x₁ r hr'.1 hr l hl]


/-! ## A batch of eight blocks -/


open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Proof.Gcm.X86_64.StitchZTo (dst sAddr pblk ctbT oAddr src_addr)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchFrom (batchFrom)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The decryption after `c` blocks: `AInvTo`, with `dst - src` in `r8`. -/
structure AInvFrom (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  r8 : s.gpr .r8 = op s₀ - sp s₀
  frame : Frame [oR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < c, blockAt s.mem (oAddr s₀ k) = ctbT s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInvFrom.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInvFrom s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInvFrom s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.gpr]; exact h.r8, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInvFrom.keys {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State}
    (hI : AInvFrom s₀ c s) : Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi]; exact (sch_frame hp.toD hI.frame).symm, by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.toD.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

/-- The ciphertext is kept. -/
theorem AInvFrom.src {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State}
    (hI : AInvFrom s₀ c s) {k : Nat} (hk : k < nb s₀) : blockAt s.mem (sAddr s₀ k) = pblk s₀ k := by
  have hw := hp.wrap_s
  exact blockAt_frame hI.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_o.sub_left (Offset.sub_base _ (by omega))
    · exact hp.s_p.sub_left (Offset.sub_base _ (by omega))

/-- `rdx + r8`, from `rdx` at ciphertext block `c` less `2 j`. -/
theorem out_base {s₀ : State} {c j : Nat} {s : State} (hj : 32 * j ≤ 16 * c)
    (hr8 : s.gpr .r8 = op s₀ - sp s₀) (hrdx : (s.gpr .rdx).toNat + 32 * j = (sp s₀).toNat + 16 * c) :
    s.gpr .rdx + s.gpr .r8 = op s₀ + BitVec.ofNat 64 (16 * c - 32 * j) := by
  have hd : s.gpr .rdx = sp s₀ + BitVec.ofNat 64 (16 * c - 32 * j) := by
    have := (s.gpr .rdx).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * c - 32 * j) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hd, hr8, BitVec.add_comm _ (op s₀ - sp s₀), ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem batchFrom_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨oAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) (hj : 32 * j ≤ 16 * c) {s : State} (hI : AInvFrom s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (sp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchFrom j g) s fun s' => AInvFrom s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨oAddr s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := Stitch.aregs_ok
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have saddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (32 * j + 16 * i) = sAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have hob := out_base hj hI.r8 hrdx
  have daddr : ∀ i, s.gpr .rdx + s.gpr .r8 + BitVec.ofNat 64 (32 * j + 16 * i) = oAddr s₀ (c + i) := fun i => by
    rw [hob, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have e32 : ∀ k, BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (32 * j + 16 * (2 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) := fun k l => by omega
  refine WP.mono (xorDataKFrom_ok .xmm13 .rdx .r8 aregs j s₂ hnd h13 (sR s₀) (oR s₀) hp.s_o
      (fun k hk => by
        rw [hg₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e32, saddr]
        exact in_sub hp.s_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [hg₂, f₂.wr, f₁.wr, hI.wr, e32, daddr]
        exact in_sub hp.o_in (by simp [aregs] at hk; omega))
      (fun k hk l hl => by
        rw [hg₂, e16, saddr]
        exact Offset.sub_base _ (by simp [aregs] at hk; omega))
      (by
        rw [hg₂, show 32 * j = 32 * j + 16 * 0 by omega, daddr, Nat.add_zero]
        exact Offset.sub_base _ (by simp [aregs]; omega))
      (by
        rw [hg₂, hob, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * c - 32 * j) (by omega),
          Nat.mod_eq_of_lt (by omega)]
        simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hg₂] at b₃ fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega, daddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      blockAt s₃.mem (oAddr s₀ (c + (2 * k + l))) =
        pblk s₀ (c + (2 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, daddr, saddr, hI.src hp (by simp [aregs] at h; omega)] at this
  have fr' : Frame [⟨oAddr s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], by rw [gs, hI.r8], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the output.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨oR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.blocks k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
      have hj : i / 2 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 2) hj (i % 2) (by omega), ks (i / 2) hj (i % 2) (by omega),
        show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]




open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo DPostTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch hk y₀
  dp dR pR cR yR bAddr addr_eq in_sub in_sub_int in_rdwr ite_t ite_f ghash_append16 blockAt_writeW_sep'
  storesK_ok pregs_get blockAt_outP GEnv QG gRegs gRegs_ok gq_ok nextD_ok FinOk store16_ok)
open VG.Proof.Gcm.X86_64.StitchZTo (sAddr pblk ctbT oAddr blocks_ctr32To)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs dA dB ordD storeCtr storeY storesK pregs)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchFrom (setupCFrom dbodyFrom)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes getLsbD_one8)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys run_sep)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## The setup -/

theorem setupCFrom_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupCFrom) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .r10 - s.gpr .r8 ∧
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
  simp only [setupCFrom, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
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

/-- The state the loop starts from. -/
structure ReadyFrom (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInvFrom s₀ 0 s
  rdx : s.gpr .rdx = sp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

/-- The setup after the powers: they are stored in the working space, then
`Y`, the counter, the increment and the pointers. -/
theorem setupTFrom_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {s₁ : State}
    (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask) (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly)
    (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupCFrom)) s₁ (ReadyFrom s₀ fun k l => s₁.lane (preg16 k) l) := by
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
  refine WP.mono (setupCFrom_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, r8, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, fun l hl => by rw [c15 l hl],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [gk _ (by decide) (by decide) (by decide) (by decide), gs _ (by decide)],
    by rw [r10, gs _ (by decide), gs _ (by decide)],
    by rw [r8, gs _ (by decide), gs _ (by decide)],
    by rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr,
    fun k hk => absurd hk (Nat.not_lt_zero _), by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩,
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 h4 => by rw [gk r h1 h2 h3 h4, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm, Nat.zero_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

/-! ## The GHASH state, kept by the output written -/

theorem QG.keepFrom {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (sp s₀).toNat + 256 * g)
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨oAddr s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_o
  have hws := hp.wrap_s
  have hwp := hp.wrap_p
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  have dO : Region.Disjoint ⟨oAddr s₀ c, 128⟩ (sR s₀) :=
    hp.s_o.symm.sub_left (Offset.sub_base _ (by omega_arith))
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = sAddr s₀ (16 * g + i) := addr_eq (by omega_arith)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact dO.symm.symm.sub_right (Offset.sub_base _ (by omega_arith)) |>.symm]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.o_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The loop of one group -/

structure DInvFrom (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInvFrom s₀ (16 * e) s
  rdx : s.gpr .rdx = sp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (pblk s₀))
  y1 : s.lane .xmm2 1 = 0

/-- The powers in the working space are kept by the output written. -/
theorem keepP {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {m m' : Mem}
    (hf : Frame [⟨oAddr s₀ c, 128⟩] m m') {k l : Nat} (hk : k < 8) (hl : l < 2) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 := by
  have hw := hp.wrap_o
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.o_p.symm.sub_right (Offset.sub_base _ (by omega_arith))) (by decide)

theorem dbodyFrom_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block}
    (hf : FinOk ordD (hk s₀) P) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : DInvFrom s₀ P e s) :
    WP isa dbodyFrom s fun s' => DInvFrom s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_s
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => pblk s₀ (16 * e + i)
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (sp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [show a + BitVec.ofNat 64 (16 * i) = sAddr s₀ (16 * e + i) from addr_eq (by omega_arith),
          hA₁.src hp (by omega_arith)]
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = sp s₀ + BitVec.ofNat 64 (256 * e + 32 * k) from addr_eq (by omega_arith)]
        exact in_sub hp.s_in (by omega_arith)
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  -- The first batch decrypts blocks 0–7 of the group, hashing them (the product with `Y` last).
  refine WP.seq (WP.mono (batchFrom_ok hp dA gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordD 0 false)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepFrom hp (by omega_arith) (by omega_arith) ha h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega_arith) (by omega_arith) hA₁
    (by rw [f₁.gpr]; show a.toNat + _ = _; omega_arith)
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hQ₂' : QG s₀ (fun _ => 0) a X P yl ordD 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch decrypts blocks 8–15, hashing them, then reduces.
  refine WP.seq (WP.mono (batchFrom_ok hp dB gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordD 4 true)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.keepFrom hp (by omega_arith) (by omega_arith) ha h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 4) (by omega_arith) (by omega_arith) hA₂
    (by rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega_arith) hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextD_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (fun h => hg' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> decide)) l hl]
  have hA' : AInvFrom s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega_arith]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fg _ (by decide) (by decide)]; exact hA₃.r8,
      by rw [fm]; exact hA₃.frame, fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd,
      by rw [fwr]; exact hA₃.wr⟩
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [gk r h2 h4]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by
      rw [fm, keepP hp (by omega_arith) hm₃ hk hl, keepP hp (by omega_arith) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith)]

/-! ## The stores -/

theorem dfinalFrom_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {P : Nat → Nat → Block} {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : DInvFrom s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (DPostTo s₀) := by
  have hw := hp.wrap_o
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₁ (by rw [l₁ _ (by decide) 0 (by decide)]; exact hm0)
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₁, hrcx, m₁, l₁ _ (by decide) 0 (by decide)] at m₂
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.o_c.sub_left (Offset.sub_base _ (by omega_arith))
  have yD : ∀ k < nb s₀, Region.Disjoint ⟨oAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.o_y.sub_left (Offset.sub_base _ (by omega_arith))
  have hb : ∀ k < nb s₀, blockAt s₂.mem (oAddr s₀ k) = ctbT s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl]
    exact hI.a.blocks k (by omega_arith)
  refine ⟨blocks_ctr32To hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide),
      Nat.add_zero, he]
  · show blockAt s₂.mem (yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4 h5
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4 h5

/-- The decryption after the setup. -/
theorem decTailFrom_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordD (hk s₀) P) {s₁ : State} (hR : ReadyFrom s₀ P s₁) :
    WP isa (.seq (.loop dbodyFrom .ae) (.block (storeCtr ++ storeY))) s₁ (DPostTo s₀) := by
  have h16 : 16 ≤ nb s₀ := hp.nb16
  have hI₁ : DInvFrom s₀ P 0 s₁ :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 h3 _ h5 => hR.gpr r h1 h2 h3 h5, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ DInvFrom s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbodyFrom s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ DInvFrom s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (dbodyFrom_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega_arith, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega_arith, e + 1, rfl, by omega_arith, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (nb s₀) s₁ ⟨0, by simp, by omega_arith, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => dfinalFrom_ok hp he hI₂)

/-! ## The whole loop -/

/-- The prepared powers `H'¹⁶⁻²ᵏ⁻ˡ` the setup loads give the products of a
decryption body. -/
def PowFinD : Prop :=
  ∀ H : Block, FinOk ordD H fun k l => StitchZP.hInvF (Spec.Gcm.hpow H (16 - 2 * k - l))

/-- The setup: the state the loop starts from, with the prepared powers. -/
theorem setupFrom_ok {s₀ : State} {np : Nat} {hn : 8 ≤ np ∧ np ≤ 24} (hp : SPreTo (CtxMode.preparedN np hn) s₀)
    (h8 : 8 ≤ np) :
    WP isa (.block Impl.Gcm.X86_64.StitchFrom.setup) s₀
      (ReadyFrom s₀ fun k l => StitchZP.hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) := by
  rw [Impl.Gcm.X86_64.StitchFrom.setup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchZRTo.setupGPTo_ok hp h8) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (setupTFrom_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun s hR => ?_
  exact { hR with pw := fun k hk l hl => by rw [hR.pw k hk l hl, pw k hk l hl] }

/-- The out-of-place decryption loop, for a prepared key context, for any
number of blocks from 16 on that is a multiple of 16. -/
theorem decR_okN (hf : PowFinD) (np : Nat) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) (h8 : 8 ≤ np := by decide) :
    Stitch.StitchFromOkM (CtxMode.preparedN np hn) Impl.Gcm.X86_64.StitchFrom.decR := fun _ hp hm =>
  WP.seq (WP.mono (setupFrom_ok hp h8) fun _ hR => decTailFrom_ok hp hm (hf _) hR)

end VG.Proof.Gcm.X86_64.StitchFrom
