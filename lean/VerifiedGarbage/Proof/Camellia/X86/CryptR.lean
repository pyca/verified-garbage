import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Camellia.X86.Prologue

/-!
# Eight blocks for 18 rounds or 24 with one copy of the rounds, on x86 (32-bit)

The modes' `crypt8R` (`Impl/Camellia/X86/Ecb.lean`): `setEnd` stores the
postwhitening's entry, found from the number of rounds in argument 1
(`RArg`), in `endSlot`; then `head`, the groups of rounds and `tail` run as
in `crypt8_ok`, the groups ending when `kp` reaches that slot's value
(`atEndS_ok`). The slot is outside what the rounds write (`ctxRegions`), so
it keeps its value through them (`Ctx.slot`).
-/

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs movR addI subI andI rorI addR argOp st movS slotAt)
open VG.Proof.Camellia (cryptWords)

/-- The number of rounds `R` in the second stack argument, readable and apart
from every writable region. -/
def RArg (s : State) (R : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4 ∧ s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 R ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.ea (argOp 1), 4⟩ r

theorem RArg.frame {s s' : State} {R : Nat} {rs : List Region} (h : RArg s R) (hesp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ s.wr, Region.Sub r r') : RArg s' R := by
  obtain ⟨hin, hv, hd⟩ := h
  have hea : s'.ea (argOp 1) = s.ea (argOp 1) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨by rw [hrd, hwr, hea]; exact hin, ?_, by rw [hwr, hea]; exact hd⟩
  rw [hea, hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨r', hr', hs⟩ := hsub r hr; exact (hd r' hr').sub_right hs) (by decide), hv]

/-- `and d, v`. -/
theorem andI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [andI d v] s = some s' ∧ s'.gpr d = s.gpr d &&& v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d &&& v) false false).setReg d (s.gpr d &&& v), rfl, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `ror d, 25`. -/
theorem ror25_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [rorI d 25] s = some s' ∧ s'.gpr d = (s.gpr d).rotateRight 25 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(s.setFlags (some ((s.gpr d).rotateRight 25).msb) none s.zf s.sf).setReg d ((s.gpr d).rotateRight 25), rfl,
    RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- The postwhitening entry's offset, `4 keySlot + 512 g`, into `edx` from
`6 g` rounds in argument 1. -/
theorem endOff_ok {s : State} {g : Nat} (hg : g = 3 ∨ g = 4) (h : RArg s (6 * g)) :
    ∃ s', runBlock isa [.mov .edx (.mem (argOp 1)), subI .edx 18, andI .edx 4, rorI .edx 25,
      addI .edx (BitVec.ofNat 32 (4 * keySlot + 1536))] s = some s' ∧
      s'.gpr .edx = BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .edx 1 h.1
  obtain ⟨s₂, e₂, v₂, -, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ .edx 18
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := andI_ok s₂ .edx 4
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ror25_ok s₃ .edx
  obtain ⟨s₅, e₅, v₅, -, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .edx (BitVec.ofNat 32 (4 * keySlot + 1536))
  refine ⟨s₅, ?_, ?_, fun r hr => by rw [o₅ r hr, o₄ r hr, o₃ r hr, o₂ r hr, o₁ r hr],
    by rw [m₅, m₄, m₃, m₂, m₁], by rw [rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show ([.mov .edx (.mem (argOp 1)), subI .edx 18, andI .edx 4, rorI .edx 25,
        addI .edx (BitVec.ofNat 32 (4 * keySlot + 1536))] : List Instr) =
      [.mov .edx (.mem (argOp 1))] ++ ([subI .edx 18] ++ ([andI .edx 4] ++ ([rorI .edx 25] ++
        [addI .edx (BitVec.ofNat 32 (4 * keySlot + 1536))]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅]
  · rw [v₅, v₄, v₃, v₂, v₁, h.2.1, keySlot_eq]
    rcases hg with rfl | rfl <;> decide

/-- The address of the postwhitening's entry, in the scratch buffer at `b`, for `g` groups. -/
def endV (b : BitVec 32) (g : Nat) : BitVec 32 := b + BitVec.ofNat 32 (4 * keySlot + 64 * (8 * g))

/-- The postwhitening's entry to its slot, from the number of rounds. -/
theorem setEnd_ok {s : State} {g : Nat} (hg : g = 3 ∨ g = 4) (hs : ScrIn s.wr (s.gpr sb)) (hra : RArg s (6 * g)) :
    ∃ s', runBlock isa setEnd s = some s' ∧ (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr (s.gpr sb) endSlot) (endV (s.gpr sb) g) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, x₁, o₁, m₁, rd₁, wr₁⟩ := endOff_ok hg hra
  obtain ⟨s₂, e₂, x₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .edx (s₁.gpr .edi)
  have b₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  have hin : InRegions s₂.wr (wordAddr (s₂.gpr sb) endSlot) 4 := by
    rw [wr₂, wr₁, b₂]; exact hs.slot (by rw [endSlot_eq, slots_eq]; decide)
  have hst : exec (st endSlot .edx) s₂ =
      some { s₂ with mem := s₂.mem.writeW (wordAddr (s₂.gpr sb) endSlot) (s₂.gpr .edx) } := by
    show s₂.store32 (wordAddr (s₂.gpr sb) endSlot) (s₂.gpr .edx) = _
    simp only [State.store32, hin, ↓reduceIte]
  have hv : s₂.gpr .edx = endV (s.gpr sb) g := by
    rw [x₂, x₁, o₁ _ (by decide)]
    show BitVec.ofNat 32 _ + s.gpr sb = _
    rw [endV, BitVec.add_comm]
    congr 2
    omega
  refine ⟨{ s₂ with mem := s₂.mem.writeW (wordAddr (s₂.gpr sb) endSlot) (s₂.gpr .edx) }, ?_,
    fun r hr => by show s₂.gpr r = _; rw [o₂ r hr, o₁ r hr], ?_, rd₂.trans rd₁, wr₂.trans wr₁⟩
  · rw [show setEnd = [.mov .edx (.mem (argOp 1)), subI .edx 18, andI .edx 4, rorI .edx 25,
        addI .edx (BitVec.ofNat 32 (4 * keySlot + 1536))] ++ ([addR .edx .edi] ++ [st endSlot .edx])
        from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app,
      show runBlock isa [addR .edx .edi] s₁ = runBlock isa [addI .edx (s₁.gpr .edi)] s₁ from rfl, e₂,
      Option.bind_some, runBlock_cons, hst, runStep_some, runBlock_nil]
  · show s₂.mem.writeW _ _ = _
    rw [b₂, hv, m₂, m₁]

/-- `mov eax, [edi + 4 endSlot]; cmp eax, kp`: Z when `kp` is at the
postwhitening's entry, whose address the slot held when the rounds began. -/
theorem atEndS_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E)
    (he : slotW s₀ endSlot = endV (s₀.gpr sb) g) : AtEndOk s₀ g atEndS := by
  intro s m hc hk hm
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  have hs := hc.scr hp.toKeyCtx
  obtain ⟨s', e', z', o', m', rd', wr'⟩ := cmpSlot_ok hs (k := endSlot) (by rw [endSlot_eq, slots_eq]; decide)
  have he' : slotW s endSlot = endV (s₀.gpr sb) g := by
    rw [hc.slot hp.scr.fit (by rw [endSlot_eq, slots_eq]; decide) (by rw [endSlot_eq, keySlot_eq]; decide)
      (by rw [endSlot_eq, grpSlot_eq]; decide)]
    exact he
  refine ⟨s', e', hc.regs (fun r _ h2 => o' r h2) m' rd' wr', by rw [AtEntry, o' _ (by decide)]; exact hk, ?_,
    fun k => by simp only [slotW, m', o' sb (by decide)]⟩
  rw [z', he', show s.gpr kp = _ from hk, endV, entry_beq _ (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)]
  simp only [Option.some.injEq, decide_eq_decide]; omega

/-- The rounds of `crypt8R` after `setEnd`: each block of the tail buffer
becomes `cryptWords g E` of it. -/
theorem cryptR_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E)
    (he : slotW s₀ endSlot = endV (s₀.gpr sb) g) :
    WP isa (.seq (.block head) (.seq (.loop (groupBodyWith atEndS) .ne) (.block tail))) s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wpW hp c₁ (atEndS_ok hp he) k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w₃⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [blk_of_words (by rw [c₃.base]; exact hp.scr.fit) w₃ hb, cryptWords]
  rfl

end VG.Proof.Camellia.X86
