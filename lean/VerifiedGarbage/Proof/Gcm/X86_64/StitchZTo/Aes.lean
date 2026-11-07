module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

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
  ⟨by rw [hI.rdi]; exact (sch_frame hp.toD hI.frame).symm, by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.toD.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

/-- The plaintext is kept. -/
theorem AInvTo.src {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {c : Nat} {s : State} (hI : AInvTo s₀ c s)
    {k : Nat} (hk : k < nb s₀) : blockAt s.mem (sAddr s₀ k) = pblk s₀ k := by
  have hw := hp.wrap_s
  exact blockAt_frame hI.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.s_o.sub_left (Offset.sub_base _ (by omega))
    · exact hp.s_p.sub_left (Offset.sub_base _ (by omega))

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
