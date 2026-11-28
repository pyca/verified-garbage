module

-- separate module: the sponge calls, whose proofs elaborate slowly, apart from the calls of `forsSign` and `xmssTree`

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopCtx
public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
public import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Instances
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. In the frame (`Ctx`): the
arguments of a call (`args_ok`, each `Arg` moving `argV` into its
register); the Keccak state at `oStream` zeroed (`zero_ok`); the calls of
`vg_keccak_absorb_scratch`, `_pad_scratch` and `_squeeze_scratch` on it,
with the working space after it (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from the
sponge functions' call lemmas, `Proof/MlKem/X86_64/KCall.lean`); and the
end of `hashM'`, which absorbs the formatted message `M′` after the pieces
before it, pads and squeezes: `SHAKE256` of the pieces and `M′`
(`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (Arg kabs kpad ksqz callA stk fCtx fCtxLen fMsg fLen)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_store wp_addi wp_mov32i ea_at)
open VG.Proof.MlKem.X86_64 (AbsorbArgs PadArgs SqueezeArgs absorb_call pad_call squeeze_call)

/-! ## Arguments -/

/-- What an argument is, for `Arg.mov`. -/
def ArgOk : Arg → Prop
  | .slot f => f + 8 ≤ 72
  | .slotOff _ _ => False
  | .scr o => o < 2 ^ 31
  | .imm v => v < 2 ^ 31
  | .sp => True
  | .ret => True

/-- The value `Arg.mov` moves, in the frame of `L`, from the state `t`. -/
def argV (L : SL) (t : State) : Arg → BitVec 64
  | .slot f => t.mem.readW (L.SP + BitVec.ofNat 64 f) 64
  | .slotOff _ _ => 0
  | .scr o => L.S + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .sp => L.SP
  | .ret => t.gpr .rax

theorem argV_congr {L : SL} {t t' : State} (hm : t'.mem = t.mem) (hx : t'.gpr .rax = t.gpr .rax) (a : Arg) :
    argV L t' a = argV L t a := by
  cases a <;> simp only [argV, hm, hx]

theorem setWidth_ofNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem stk_ea (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  congr 1

theorem argMov_ok {L : SL} {t : State} (hb : t.gpr .rbx = L.S) (hsp : t.gpr .rsp = L.SP)
    (hin : ∀ f, f + 8 ≤ 72 → InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 f) 8)
    {d : Reg} {a : Arg} (ha : ArgOk a) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Upd t t' d (argV L t a) → WP isa (.block is) t' Q) :
    WP isa (.block (a.mov d ++ is)) t Q := by
  cases a with
  | slot f =>
    exact wp_movm (a := L.SP + BitVec.ofNat 64 f) (by rw [stk_ea, hsp]) (hin f ha) k
  | slotOff f o => exact absurd ha id
  | scr o =>
    refine wp_mov fun t₁ u₁ => wp_addi fun t₂ u₂ => k t₂ ⟨?_, fun r h => by rw [u₂.other r h, u₁.other r h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.gpr, hb, Levels.sx_ofNat ha]; rfl
  | imm v =>
    refine wp_mov32i fun t₁ u₁ => k t₁ ?_
    have := setWidth_ofNat32 (v := v) (by have : v < 2 ^ 31 := ha; omega)
    show Upd t t₁ d (BitVec.ofNat 64 v)
    rw [← this]; exact u₁
  | sp => exact wp_mov fun t₁ u₁ => k t₁ (by rw [show argV L t .sp = t.gpr .rsp by rw [hsp]; rfl]; exact u₁)
  | ret => exact wp_mov fun t₁ u₁ => k t₁ u₁

/-- A block of argument moves, to distinct registers other than `rax`, `rbx` and `rsp`. -/
theorem args_ok₀ {L : SL} : ∀ (ps : List (Reg × Arg)) {t : State} {Q : State → Prop},
    t.gpr .rbx = L.S → t.gpr .rsp = L.SP →
    (∀ f, f + 8 ≤ 72 → InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 f) 8) →
    (∀ p ∈ ps, ArgOk p.2 ∧ p.1 ≠ .rax ∧ p.1 ≠ .rbx ∧ p.1 ≠ .rsp) → (ps.map Prod.fst).Nodup →
    (∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r, r ∉ ps.map Prod.fst → t'.gpr r = t.gpr r) →
      (∀ p ∈ ps, t'.gpr p.1 = argV L t p.2) → Q t') →
    WP isa (.block (ps.flatMap fun (d, a) => a.mov d)) t Q
  | [], t, _, _, _, _, _, _, k => WP.block_nil (k t rfl rfl rfl (fun _ _ => rfl) fun _ h => absurd h List.not_mem_nil)
  | (d, a) :: ps, t, Q, hb, hsp, hin, hok, hnd, k => by
    simp only [List.flatMap_cons]
    obtain ⟨ha, hd1, hd2, hd3⟩ := hok (d, a) (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine argMov_ok hb hsp hin ha fun t₁ u₁ => ?_
    have hrd : t₁.rd ++ t₁.wr = t.rd ++ t.wr := by rw [u₁.rd, u₁.wr]
    refine args_ok₀ ps (by rw [u₁.other _ (Ne.symm hd2), hb]) (by rw [u₁.other _ (Ne.symm hd3), hsp])
      (fun f hf => by rw [hrd]; exact hin f hf) (fun p hp => hok p (List.mem_cons_of_mem _ hp)) hnd.2
      fun t' hm hr hw hg hv => k t' (by rw [hm, u₁.mem]) (by rw [hr, u₁.rd]) (by rw [hw, u₁.wr]) (fun r hr' => ?_)
        fun p hp => ?_
    · simp only [List.map_cons, List.mem_cons, not_or] at hr'
      rw [hg r hr'.2, u₁.other r hr'.1]
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [hg d hnd.1, u₁.gpr]
      · rw [hv p hp, argV_congr u₁.mem (u₁.other _ (Ne.symm hd1))]

/-- The bits of MXCSR that `abiPreserved` keeps. -/
abbrev MxEq (t t' : State) : Prop := t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10

theorem MxEq.trans {a b c : State} (h₁ : MxEq a b) (h₂ : MxEq b c) : MxEq a c := Eq.trans h₂ h₁

theorem MxEq.of_eq {a b : State} (h : b.mxcsr = a.mxcsr) : MxEq a b := by
  show b.mxcsr.extractLsb' 6 10 = a.mxcsr.extractLsb' 6 10; rw [h]

theorem args_nm (ps : List (Reg × Arg)) :
    (Code.block (ps.flatMap fun (d, a) => a.mov d) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp only [instrs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a <;> simp only [Arg.mov, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
    (try rcases hi with rfl | rfl) <;> (try subst hi) <;> rfl

theorem args_ok {L : SL} (ps : List (Reg × Arg)) {t : State} {Q : State → Prop}
    (hb : t.gpr .rbx = L.S) (hsp : t.gpr .rsp = L.SP)
    (hin : ∀ f, f + 8 ≤ 72 → InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 f) 8)
    (hok : ∀ p ∈ ps, ArgOk p.2 ∧ p.1 ≠ .rax ∧ p.1 ≠ .rbx ∧ p.1 ≠ .rsp) (hnd : (ps.map Prod.fst).Nodup)
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r, r ∉ ps.map Prod.fst → t'.gpr r = t.gpr r) →
      (∀ p ∈ ps, t'.gpr p.1 = argV L t p.2) → MxEq t t' → Q t') :
    WP isa (.block (ps.flatMap fun (d, a) => a.mov d)) t Q :=
  WP.mono_mx (args_nm ps) (args_ok₀ ps hb hsp hin hok hnd (Q := fun t' => t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ (∀ r, r ∉ ps.map Prod.fst → t'.gpr r = t.gpr r) ∧ ∀ p ∈ ps, t'.gpr p.1 = argV L t p.2)
    fun _ a b c d e => ⟨a, b, c, d, e⟩) fun t' ⟨a, b, c, d, e⟩ hm => k t' a b c d e (MxEq.of_eq hm)

open VG.Proof.MlKem.X86_64 (absorb_pre pad_pre squeeze_pre absorb_nosp pad_nosp squeeze_nosp absorb_depth
  pad_depth squeeze_depth ofNat_toNat' rate_lt callEntry_repr callEntry_bytesAt callEntry_stateAt ce_gpr)

/-- `absorb_call`, with what the call keeps of MXCSR. -/
theorem absorb_callMx {s : State} {st dp scr : Addr} {rate pos len : Nat} (h : AbsorbArgs s st dp scr rate pos len)
    (hc : Covers ([⟨dp, len⟩] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem st rate (msg ++ bytesAt s.mem dp len)) →
      (s'.gpr .rax).toNat = (pos + len) % rate → MxEq s s' → Q s') :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call_mx (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp
    (by rw [absorb_depth]; decide) (absorb_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ hmx
  simp only [State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost hrax
  refine hQ s' hrd hwr hcs (by rw [absorb_depth] at hf; simpa using hf) (fun msg hm hp => ?_)
    (by rw [← hg₂ _ (by decide)]; exact hrax) hmx
  have := hpost msg ((callEntry_repr s h.k_st).mpr hm) hp
  rwa [callEntry_bytesAt s h.hlen h.k_d] at this

/-- `pad_call`, with what the call keeps of MXCSR. -/
theorem pad_callMx {s : State} {st scr : Addr} {rate pos : Nat} (h : PadArgs s st scr rate pos)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .rcx).setWidth 8) msg)) → MxEq s s' → Q s') :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call_mx (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp
    (by rw [pad_depth]; decide) (pad_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₂, ofNat_toNat' hr,
    ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hcs (by rw [pad_depth] at hf; simpa using hf)
    (fun msg hm hp => hpost msg ((callEntry_repr s h.k_st).mpr hm) hp) hmx

/-- `squeeze_call`, with what the call keeps of MXCSR. -/
theorem squeeze_callMx {s : State} {st out scr : Addr} {rate pos len : Nat} (h : SqueezeArgs s st out scr rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len → MxEq s s' → Q s') :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s Q := by
  have hr := rate_lt h.hrate
  refine WP.call_mx (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]; decide) (squeeze_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, _⟩ hmx
  simp only [State.withRegions_gpr, State.withRegions_mem, ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr s (by decide : Reg.rsi ≠ .rsp), ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    ce_gpr s (by decide : Reg.rcx ≠ .rsp), ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)] at hpost
  refine hQ s' hrd hwr hcs (by rw [squeeze_depth] at hf; simpa using hf) ?_ hmx
  rw [hpost, callEntry_stateAt s h.k_st]

/-! ## The Keccak state -/

theorem oStream_eq : Layout.oStream = 30560 := rfl

/-- The Keccak state, its working space, and both. -/
abbrev stR (L : SL) : Region := ⟨at' L.S Layout.oStream, 200⟩
abbrev swR (L : SL) : Region := ⟨at' L.S (Layout.oStream + 200), 640⟩
abbrev sAll (L : SL) : Region := ⟨at' L.S Layout.oStream, 840⟩

/-- A part of `scratch` above the lanes, apart from the saved registers. -/
theorem free_hi {L : SL} (hL : L.Ok) {o l : Nat} (h₁ : Layout.oN ≤ o) (h₂ : o + l ≤ 65536)
    (h₃ : o + l ≤ Impl.SlhDsa.X86_64.Shake.oKgSave ∨ Impl.SlhDsa.X86_64.Shake.oKgSave + 48 ≤ o) :
    Free L ⟨at' L.S o, l⟩ := by
  have := hL.n32
  have e0 : Layout.oN = 12640 := rfl
  have e1 : Layout.oKeys = 3168 := rfl
  have e3 : Impl.SlhDsa.X86_64.Shake.oKgSave = 34080 := rfl
  have e4 : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have e5 : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  rw [e0] at h₁; rw [e3] at h₃
  refine .inl ⟨hL.scr_sub h₂, fun q hq => ?_⟩
  simp only [SL.prot, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_range] at hq
  rcases hq with ((rfl | rfl | rfl) | ⟨k, hk, rfl | rfl⟩)
  · exact Levels.disj_scr L.S (by omega) h₂ (by omega)
  · exact Levels.disj_scr L.S (by rw [e1]; omega) h₂ (by rw [e1]; omega)
  · exact Levels.disj_scr L.S (by rw [e3]; omega) h₂ (by rw [e3]; omega)
  · exact Levels.disj_scr L.S (by rw [e4]; omega) h₂ (by rw [e4]; omega)
  · exact Levels.disj_scr L.S (by rw [e5]; omega) h₂ (by rw [e5]; omega)

theorem sAll_free {L : SL} (hL : L.Ok) : Free L (sAll L) :=
  free_hi hL (by decide) (by rw [oStream_eq]; omega) (.inl (by decide))

theorem sub_sAll (L : SL) {o l : Nat} (h₁ : Layout.oStream ≤ o) (h₂ : o + l ≤ Layout.oStream + 840) :
    Region.Sub ⟨at' L.S o, l⟩ (sAll L) := Offset.sub L.S h₁ h₂

theorem free_of_sAll {L : SL} (hL : L.Ok) {r : Region} (h : Region.Sub r (sAll L)) : Free L r := by
  rcases sAll_free hL with ⟨h₁, h₂⟩ | h₁ | h₁
  · exact .inl ⟨fun a ha => h₁ a (h a ha), fun q hq => (h₂ q hq).sub_left h⟩
  · exact .inr (.inl fun a ha => h₁ a (h a ha))
  · exact .inr (.inr fun a ha => h₁ a (h a ha))

theorem below16_free {L : SL} (hL : L.Ok) (hst : 8 ≤ L.st) : Free L (below L.SP 16) :=
  .inr (.inl (SL.Ok.below_cs L (by omega) hL))

/-- The 25 lanes of the state, zeroed. -/
theorem zero_ok₀ {L : SL} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → stateAt t'.mem (at' L.S Layout.oStream) = Spec.Sha3.zero →
      Frame [stR L] t.mem t'.mem → Q t') :
    WP isa (.block Impl.SlhDsa.X86_64.Shake.zeroState) t Q := by
  unfold Impl.SlhDsa.X86_64.Shake.zeroState
  refine wp_mov32i fun t₁ u₁ => ?_
  have hax : t₁.gpr .rax = 0 := by rw [u₁.gpr]; rfl
  have hc₁ : Ctx L g m₀ t₁ := hc.regs u₁.rd u₁.wr u₁.mem fun r hr => u₁.other r (by
    intro e; subst e; exact absurd hr (by decide))
  have hS : (⟨L.S, 2 ^ 16⟩ : Region) ∈ t₁.wr := hc₁.inScr
  refine WP.mono (Levels.wp_rangeMap (P := fun j u => u.gpr = t₁.gpr ∧ u.rd = t₁.rd ∧ u.wr = t₁.wr ∧
      (∀ i < j, u.mem.readW (at' L.S (Layout.oStream + 8 * i)) 64 = 0) ∧ Frame [stR L] t₁.mem u.mem) 25
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj u ⟨hg, hr, hw, hz, hf⟩ => ?_)
    fun u ⟨hg, hr, hw, hz, hf⟩ => ?_
  · refine wp_store (a := at' L.S (Layout.oStream + 8 * j)) (by rw [ea_at, hg, hc₁.rbx])
      (by rw [hw, oStream_eq]; exact Levels.in_scr hS (by omega)) fun u' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', hg], by rw [r', hr], by rw [w', hw], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, hg, hax]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by rw [oStream_eq]; omega)
          (by rw [oStream_eq]; omega)) (by decide), hz i (by omega)]
    · rw [m']
      exact hf.writeW (List.mem_singleton_self _) _ (by
        rw [← Levels.at_add]; exact Offset.contains_base _ (by omega) (by omega))
  · have hf' : Frame [stR L] t.mem u.mem := by rw [← u₁.mem]; exact hf
    refine k u (hc.of_frame hL (by rw [hr, u₁.rd]) (by rw [hw, u₁.wr]) (by rw [hg, u₁.other _ (by decide)])
      (by rw [hg, u₁.other _ (by decide)]) (fun r hr' _ _ => by
        rw [hg, u₁.other _ (by intro e; subst e; exact absurd hr' (by decide))]) hf'
      fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact free_of_sAll hL (sub_sAll L (Nat.le_refl _) (by omega))) ?_ hf'
    apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    rw [Levels.at_add]
    exact hz i hi

theorem zero_nm : (Code.block Impl.SlhDsa.X86_64.Shake.zeroState : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp [Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Shake.zeroState, List.all_map, loadsMxcsr]

theorem zero_ok {L : SL} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → stateAt t'.mem (at' L.S Layout.oStream) = Spec.Sha3.zero →
      Frame [stR L] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (.block Impl.SlhDsa.X86_64.Shake.zeroState) t Q :=
  WP.mono_mx zero_nm (zero_ok₀ hL hc (Q := fun t' => Ctx L g m₀ t' ∧
      stateAt t'.mem (at' L.S Layout.oStream) = Spec.Sha3.zero ∧ Frame [stR L] t.mem t'.mem)
    fun _ a b c => ⟨a, b, c⟩) fun t' ⟨a, b, c⟩ hm => k t' a b c (MxEq.of_eq hm)

/-! ## The calls -/

section
variable {L : SL} (hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)

include hc in
theorem inSlots : ∀ f, f + 8 ≤ 72 → InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 f) 8 :=
  fun _ h => hc.inFr h

include hc in
theorem stR_cov : Covers [stR L, swR L] t.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hc.wr]
  rcases hr with rfl | rfl
  · exact ⟨L.SCR, by simp, Layout.oStream, rfl, by show Layout.oStream + 200 ≤ 65536; rw [oStream_eq]; omega⟩
  · exact ⟨L.SCR, by simp, Layout.oStream + 200, rfl, by show Layout.oStream + 200 + 640 ≤ 65536; rw [oStream_eq]; omega⟩

omit hL hc in
theorem st_sw : Region.Disjoint (stR L) (swR L) :=
  Levels.disj_scr L.S (by omega) (by rw [oStream_eq]; omega) (by rw [oStream_eq]; omega)

include hL hc in
theorem k16_st (hst : 8 ≤ L.st) : (below (t.gpr .rsp) 16).Disjoint (stR L) := by
  rw [hc.rsp]
  exact (hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))

include hL hc in
theorem k16_sw (hst : 8 ≤ L.st) : (below (t.gpr .rsp) 16).Disjoint (swR L) := by
  rw [hc.rsp]
  exact (hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))

include hL hc in
/-- A call of `vg_keccak_absorb_scratch` on `l` bytes at `A`, readable and
apart from the state, its working space and the 16 bytes below `rsp`. -/
theorem kabs_ok (hst : 8 ≤ L.st) {src len pos : Arg} (hs : ArgOk src) (hl : ArgOk len) (hp : ArgOk pos)
    {A : Addr} {l : Nat} (hA : argV L t src = A) (hlv : argV L t len = BitVec.ofNat 64 l) (hl64 : l < 2 ^ 64)
    (hAin : Covers [⟨A, l⟩] (t.rd ++ t.wr)) (hAst : Region.Disjoint ⟨A, l⟩ (stR L))
    (hAsw : Region.Disjoint ⟨A, l⟩ (swR L)) (hAk : Region.Disjoint (below L.SP 16) ⟨A, l⟩)
    {msg : List Byte} (hR : Repr t.mem (at' L.S Layout.oStream) 136 msg)
    (hpv : argV L t pos = BitVec.ofNat 64 (msg.length % 136)) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → Repr t'.mem (at' L.S Layout.oStream) 136 (msg ++ bytesAt t.mem A l) →
      (t'.gpr .rax).toNat = (msg.length % 136 + l) % 136 → Frame [stR L, swR L, below L.SP 16] t.mem t'.mem →
      MxEq t t' → Q t') :
    WP isa (kabs src len pos) t Q := by
  unfold kabs callA
  refine WP.seq (args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, src),
    (.r8, len), (.r9, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv hmx₁ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hs | exact hl | exact hp | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
    (.rcx, src), (.r8, len), (.r9, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have ha : AbsorbArgs t₁ (at' L.S Layout.oStream) A (at' L.S (Layout.oStream + 200)) 136 (msg.length % 136) l := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, Nat.mod_lt _ (by decide), hl64, st_sw, hAst, hAsw, ?_, ?_, ?_⟩
    · exact v (.rdi) (.scr Layout.oStream) (.head _)
    · exact v (.rsi) (.imm 136) (.tail _ (.head _))
    · rw [v (.rdx) pos (.tail _ (.tail _ (.head _))), hpv]
    · rw [v (.rcx) src (.tail _ (.tail _ (.tail _ (.head _)))), hA]
    · rw [v (.r8) len (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), hlv]
    · exact v (.r9) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    · rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst
    · rw [hsp₁]; exact hAk
    · rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst
  have hcw : Covers [stR L, swR L] t₁.wr := by rw [hw]; exact stR_cov hc
  refine absorb_callMx ha (Covers.append_left (by rw [hr, hw]; exact hAin) (Covers.right hcw)) hcw
    fun t' hrd hwr hcs hf hRep hrax hmx => ?_
  have hcs' : ∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r := fun r hr' => hg r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [List.map_cons, List.map_nil]
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [hsp₁] at hf
  have hc₁ : Ctx L g m₀ t₁ := hc.regs hr hw hm hcs'
  refine k t' (hc₁.of_frame hL hrd hwr (by rw [hcs _ (by decide)]) (by rw [hcs _ (by decide)])
      (fun r hr' _ _ => hcs r hr') hf fun r hr' => ?_) ?_ hrax (by rw [← hm]; exact hf) (hmx₁.trans hmx)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact free_of_sAll hL (sub_sAll L (Nat.le_refl _) (by omega))
    · exact free_of_sAll hL (sub_sAll L (by omega) (by omega))
    · exact below16_free hL hst
  · rw [← hm]; exact hRep msg (by rw [hm]; exact hR) rfl

include hL hc in
/-- A call of `vg_keccak_pad_scratch`, with SHAKE's suffix. -/
theorem kpad_ok (hst : 8 ≤ L.st) {pos : Arg} (hp : ArgOk pos) {msg : List Byte}
    (hR : Repr t.mem (at' L.S Layout.oStream) 136 msg)
    (hpv : argV L t pos = BitVec.ofNat 64 (msg.length % 136)) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' →
      stateAt t'.mem (at' L.S Layout.oStream) = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg) →
      Frame [stR L, swR L, below L.SP 16] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (kpad pos) t Q := by
  unfold kpad callA
  refine WP.seq (args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos), (.rcx, .imm 0x1f),
    (.r8, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv hmx₁ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hp | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, pos),
    (.rcx, .imm 0x1f), (.r8, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have ha : PadArgs t₁ (at' L.S Layout.oStream) (at' L.S (Layout.oStream + 200)) 136 (msg.length % 136) :=
    ⟨v (.rdi) (.scr Layout.oStream) (.head _), v (.rsi) (.imm 136) (.tail _ (.head _)), by rw [v (.rdx) pos (.tail _ (.tail _ (.head _))), hpv], v (.r8) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by decide,
      Nat.mod_lt _ (by decide), st_sw, by rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst,
      by rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst⟩
  have hcw : Covers [stR L, swR L] t₁.wr := by rw [hw]; exact stR_cov hc
  have hcx : t₁.gpr .rcx = BitVec.ofNat 64 0x1f := v (.rcx) (.imm 0x1f) (.tail _ (.tail _ (.tail _ (.head _))))
  refine pad_callMx ha (Covers.append_left Covers.nil (Covers.right hcw)) hcw fun t' hrd hwr hcs hf hS hmx => ?_
  have hcs' : ∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r := fun r hr' => hg r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [List.map_cons, List.map_nil]
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [hsp₁] at hf
  have hc₁ : Ctx L g m₀ t₁ := hc.regs hr hw hm hcs'
  refine k t' (hc₁.of_frame hL hrd hwr (by rw [hcs _ (by decide)]) (by rw [hcs _ (by decide)])
      (fun r hr' _ _ => hcs r hr') hf fun r hr' => ?_) ?_ (by rw [← hm]; exact hf) (hmx₁.trans hmx)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact free_of_sAll hL (sub_sAll L (Nat.le_refl _) (by omega))
    · exact free_of_sAll hL (sub_sAll L (by omega) (by omega))
    · exact below16_free hL hst
  · rw [hS msg (by rw [hm]; exact hR) rfl, hcx]; rfl

include hL hc in
/-- A call of `vg_keccak_squeeze_scratch` of `len` bytes from the start of a
block to `D`, writable and apart from the state, its working space and the
16 bytes below `rsp`. -/
theorem ksqz_ok (hst : 8 ≤ L.st) {dst : Arg} (hd : ArgOk dst) {len : Nat} (hlen : len < 2 ^ 31) {D : Addr}
    (hD : argV L t dst = D) (hDin : Covers [⟨D, len⟩] t.wr) (hDst : Region.Disjoint (stR L) ⟨D, len⟩)
    (hDsw : Region.Disjoint ⟨D, len⟩ (swR L)) (hDk : Region.Disjoint (below L.SP 16) ⟨D, len⟩)
    (hDf : Free L ⟨D, len⟩) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' →
      bytesAt t'.mem D len = squeezeFrom 136 (stateAt t.mem (at' L.S Layout.oStream)) 0 len →
      Frame [stR L, ⟨D, len⟩, swR L, below L.SP 16] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (ksqz dst len) t Q := by
  unfold ksqz callA
  refine WP.seq (args_ok (L := L) [(.rdi, .scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0), (.rcx, dst),
    (.r8, .imm len), (.r9, .scr (Layout.oStream + 200))] hc.rbx hc.rsp (inSlots hc) (fun p hp' => ?_)
    (by simp only [List.map_cons, List.map_nil]; decide)
    fun t₁ hm hr hw hg hv hmx₁ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [ArgOk] <;> first | exact hd | exact hlen | decide | (rw [oStream_eq]; decide)
  have v := fun (d : Reg) (a : Arg) (h : (d, a) ∈ [(Reg.rdi, Arg.scr Layout.oStream), (.rsi, .imm 136), (.rdx, .imm 0),
    (.rcx, dst), (.r8, .imm len), (.r9, .scr (Layout.oStream + 200))]) => hv (d, a) h
  have hsp₁ : t₁.gpr .rsp = L.SP := by rw [hg _ (by simp only [List.map_cons, List.map_nil]; decide), hc.rsp]
  have ha : SqueezeArgs t₁ (at' L.S Layout.oStream) D (at' L.S (Layout.oStream + 200)) 136 0 len :=
    ⟨v (.rdi) (.scr Layout.oStream) (.head _), v (.rsi) (.imm 136) (.tail _ (.head _)), v (.rdx) (.imm 0) (.tail _ (.tail _ (.head _))), by rw [v (.rcx) dst (.tail _ (.tail _ (.tail _ (.head _)))), hD], v (.r8) (.imm len) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
      v (.r9) (.scr (Layout.oStream + 200)) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by decide, Nat.zero_le _, by omega, hDst, st_sw, hDsw,
      by rw [hsp₁, ← hc.rsp]; exact k16_st hL hc hst, by rw [hsp₁]; exact hDk,
      by rw [hsp₁, ← hc.rsp]; exact k16_sw hL hc hst⟩
  have hcw : Covers [stR L, ⟨D, len⟩, swR L] t₁.wr := by
    rw [hw]
    have h2 := stR_cov hc
    have hs : Covers [stR L] t.wr :=
      (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans h2
    have hw' : Covers [swR L] t.wr :=
      (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans h2
    exact Covers.cons hs (Covers.cons hDin hw')
  refine squeeze_callMx ha (Covers.append_left Covers.nil (Covers.right hcw)) hcw fun t' hrd hwr hcs hf ho hmx => ?_
  have hcs' : ∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r := fun r hr' => hg r (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [List.map_cons, List.map_nil]
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [hsp₁] at hf
  have hc₁ : Ctx L g m₀ t₁ := hc.regs hr hw hm hcs'
  refine k t' (hc₁.of_frame hL hrd hwr (by rw [hcs _ (by decide)]) (by rw [hcs _ (by decide)])
      (fun r hr' _ _ => hcs r hr') hf fun r hr' => ?_) (by rw [ho, hm]) (by rw [← hm]; exact hf)
      (hmx₁.trans hmx)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact free_of_sAll hL (sub_sAll L (Nat.le_refl _) (by omega))
    · exact hDf
    · exact free_of_sAll hL (sub_sAll L (by omega) (by omega))
    · exact below16_free hL hst

/-! ## `hashM'` -/

theorem sub_st (L : SL) (X : Region) : ∀ x ∈ [stR L], ∃ y ∈ [sAll L, X, below L.SP 16], Region.Sub x y := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx
  exact ⟨_, by simp, sub_sAll L (Nat.le_refl _) (by omega)⟩

theorem sub_call (L : SL) (X : Region) :
    ∀ x ∈ [stR L, swR L, below L.SP 16], ∃ y ∈ [sAll L, X, below L.SP 16], Region.Sub x y := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, by simp, sub_sAll L (Nat.le_refl _) (by omega)⟩
  · exact ⟨_, by simp, sub_sAll L (by omega) (by omega)⟩
  · exact ⟨_, by simp, fun a h => h⟩

/-- The formatted message `M′`: the frame's two bytes, then the context
string and the message as on entry. -/
abbrev Mp (L : SL) (m₀ : Mem) : List Byte :=
  [0, BitVec.ofNat 8 L.ctxLen.toNat] ++ bytesAt m₀ L.ctx L.ctxLen.toNat ++ bytesAt m₀ L.msg L.len.toNat

theorem shake256_eq (M : List Byte) (d : Nat) :
    Spec.Sha3.shake256 M d = squeezeFrom 136 (absorb 136 (pad 136 Spec.Sha3.shakeSuffix M)) 0 d := by
  rw [Proof.Sha3.Instances.squeezeFrom_zero]; rfl

include hL hc in
/-- The end of `hashM'`: `M′` after the pieces `pre` (at most 133 bytes)
already absorbed, padded and squeezed to `D`. -/
theorem tail_ok (hst : 8 ≤ L.st) {pre : List Byte} (hpl : pre.length + 2 < 136)
    (hR : Repr t.mem (at' L.S Layout.oStream) 136 pre) {q : Nat} (hq : q = pre.length)
    {dst : Arg} (hd : ArgOk dst) {len : Nat} (hlen : len < 2 ^ 31) {D : Addr}
    (hD : ∀ t', Ctx L g m₀ t' → argV L t' dst = D) (hDin : Covers [⟨D, len⟩] t.wr)
    (hDst : Region.Disjoint (stR L) ⟨D, len⟩) (hDsw : Region.Disjoint ⟨D, len⟩ (swR L))
    (hDk : Region.Disjoint (below L.SP 16) ⟨D, len⟩) (hDf : Free L ⟨D, len⟩) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → bytesAt t'.mem D len = Spec.Sha3.shake256 (pre ++ Mp L m₀) len →
      Frame [sAll L, ⟨D, len⟩, below L.SP 16] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (.seq (kabs .sp (.imm 2) (.imm q)) (.seq (kabs (.slot fCtx) (.slot fCtxLen) .ret)
      (.seq (kabs (.slot fMsg) (.slot fLen) .ret) (.seq (kpad .ret) (ksqz dst len))))) t Q := by
  have hnB := hL.nB
  have hsub : ∀ {r : Region}, Region.Sub r (sAll L) → ∀ x ∈ [r], ∃ y ∈ [sAll L, ⟨D, len⟩, below L.SP 16], Region.Sub x y :=
    fun h x hx => by simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, by simp, h⟩
  have hF : ∀ {m m' : Mem}, Frame [stR L, swR L, below L.SP 16] m m' → Frame [sAll L, ⟨D, len⟩, below L.SP 16] m m' :=
    fun f => f.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨_, by simp, sub_sAll L (Nat.le_refl _) (by omega)⟩
      · exact ⟨_, by simp, sub_sAll L (by omega) (by omega)⟩
      · exact ⟨_, by simp, fun a h => h⟩
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  -- the frame's two bytes
  have e0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
  refine WP.seq (kabs_ok hL hc hst (src := .sp) (len := .imm 2) (pos := .imm q) trivial (by dsimp only [ArgOk]; decide)
    (by show q < 2 ^ 31; omega) (A := L.SP) (l := 2) rfl rfl (by decide)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by rw [hc.rd, hc.wr]; simp, 0, by simp, by show 0 + 2 ≤ 72; omega⟩)
    (by have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (hL.scr_sub (o := Layout.oStream) (l := 200)
      (by rw [oStream_eq]; omega)); simpa only [e0] using this)
    (by have := (hL.fr_scr (d := 0) (n := 2) (by omega)).sub_right (hL.scr_sub (o := Layout.oStream + 200) (l := 640)
      (by rw [oStream_eq]; omega)); simpa only [e0] using this)
    (Offset.base_disjoint_below L.SP (by omega)).symm hR (by show BitVec.ofNat 64 q = _; rw [hq, Nat.mod_eq_of_lt (by omega)])
    fun t₁ hc₁ hR₁ hx₁ hf₁ mx₁ => ?_)
  rw [hc.hdr] at hR₁
  -- the context string
  have hctx : bytesAt t₁.mem L.ctx L.ctxLen.toNat = bytesAt m₀ L.ctx L.ctxLen.toNat :=
    hc₁.bytesAt_eq hL.sCtx hL.kCtx hL.gCtx (by have := hL.nCtx; omega)
  refine WP.seq (kabs_ok hL hc₁ hst (src := .slot fCtx) (len := .slot fCtxLen) (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide)
    trivial (A := L.ctx) (l := L.ctxLen.toNat) hc₁.pCtx (by show t₁.mem.readW (L.SP + BitVec.ofNat 64 32) 64 = _; rw [hc₁.pCtxLen, Levels.ofNat_toNat64]) (BitVec.isLt _)
    (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hc₁.rd]; simp))
    (hL.sCtx.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    (hL.sCtx.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))) (k16 hL.kCtx) hR₁
    (by
      show t₁.gpr .rax = _
      rw [← Levels.ofNat_toNat64 (t₁.gpr .rax), hx₁, List.length_append, Nat.mod_eq_of_lt (a := pre.length) (by omega)]
      simp)
    fun t₂ hc₂ hR₂ hx₂ hf₂ mx₂ => ?_)
  rw [hctx] at hR₂
  -- the message
  have hmsg : bytesAt t₂.mem L.msg L.len.toNat = bytesAt m₀ L.msg L.len.toNat :=
    hc₂.bytesAt_eq hL.sMsg hL.kMsg hL.gMsg (by have := hL.nMsg; omega)
  refine WP.seq (kabs_ok hL hc₂ hst (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (by dsimp only [ArgOk]; decide) (by dsimp only [ArgOk]; decide)
    trivial (A := L.msg) (l := L.len.toNat) hc₂.pMsg (by show t₂.mem.readW (L.SP + BitVec.ofNat 64 48) 64 = _; rw [hc₂.pLen, Levels.ofNat_toNat64]) (BitVec.isLt _)
    (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hc₂.rd]; simp))
    (hL.sMsg.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    (hL.sMsg.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega))) (k16 hL.kMsg) hR₂
    (by
      show t₂.gpr .rax = _
      rw [← Levels.ofNat_toNat64 (t₂.gpr .rax), hx₂]
      simp only [Nat.mod_add_mod, List.length_append, bytesAt_length'])
    fun t₃ hc₃ hR₃ hx₃ hf₃ mx₃ => ?_)
  rw [hmsg] at hR₃
  refine WP.seq (kpad_ok hL hc₃ hst (pos := .ret) trivial hR₃
    (by
      show t₃.gpr .rax = _
      rw [← Levels.ofNat_toNat64 (t₃.gpr .rax), hx₃]
      simp only [Nat.mod_add_mod, List.length_append, bytesAt_length'])
    fun t₄ hc₄ hS₄ hf₄ mx₄ => ?_)
  refine ksqz_ok hL hc₄ hst hd hlen (hD t₄ hc₄) (by rw [hc₄.wr, ← hc.wr]; exact hDin) hDst hDsw hDk hDf
    fun t₅ hc₅ ho hf₅ mx₅ => k t₅ hc₅ ?_ ?_ (mx₁.trans (mx₂.trans (mx₃.trans (mx₄.trans mx₅))))
  · rw [ho, hS₄, shake256_eq]
    simp only [Mp, List.append_assoc]
  · refine (hF hf₁).trans ((hF hf₂).trans ((hF hf₃).trans ((hF hf₄).trans (hf₅.sub fun x hx => ?_))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, sub_sAll L (Nat.le_refl _) (by omega)⟩
    · exact ⟨_, by simp, fun a h => h⟩
    · exact ⟨_, by simp, sub_sAll L (by omega) (by omega)⟩
    · exact ⟨_, by simp, fun a h => h⟩

include hL hc in
/-- `R = PRF_msg(SK.prf, addrnd, M′)` to the signature's first `n` bytes. -/
theorem hashR_ok {p : Spec.SlhDsa.Params} (hn : L.n = p.n) (hst : 8 ≤ L.st) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' →
      bytesAt t'.mem L.sig p.n = Spec.Sha3.shake256 (bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 1)) p.n ++
        bytesAt m₀ L.rnd p.n ++ Mp L m₀) p.n →
      Frame [sAll L, ⟨L.sig, p.n⟩, below L.SP 16] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (Impl.SlhDsa.X86_64.Shake.hashM' p [.scr Layout.oSkPrf, .slot Impl.SlhDsa.X86_64.Shake.fRnd]
      (.slot Impl.SlhDsa.X86_64.Shake.fSig) p.n) t Q := by
  have hn32 := hL.n32
  rw [hn] at hn32
  have hnB := hL.nB
  have eP : Layout.oSkPrf = 3200 := rfl
  simp only [Impl.SlhDsa.X86_64.Shake.hashM', List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil,
    List.length_cons, List.length_nil]
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  refine WP.seq (zero_ok hL hc fun t₀ hc₀ hz hf₀ mx₀ => ?_)
  have hR₀ : Repr t₀.mem (at' L.S Layout.oStream) 136 [] := by
    show stateAt t₀.mem _ = Proof.Sha3.Rep 136 []
    rw [Proof.Sha3.rep_nil, hz]
  -- `SK.prf`
  refine WP.seq (kabs_ok hL hc₀ hst (src := .scr Layout.oSkPrf) (len := .imm p.n) (pos := .imm (p.n * 0))
    (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
    (A := at' L.S Layout.oSkPrf) (l := p.n) rfl rfl (by omega)
    (Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc₀.wr]; simp, Layout.oSkPrf, rfl, by show _ + p.n ≤ 65536; rw [eP]; omega⟩))
    (Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega))
    (Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega))
    ((hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eP]; omega)))
    hR₀ (by simp [argV]) fun t₁ hc₁ hR₁ hx₁ hf₁ mx₁ => ?_)
  -- `addrnd`
  refine WP.seq (kabs_ok hL hc₁ hst (src := .slot Impl.SlhDsa.X86_64.Shake.fRnd) (len := .imm p.n)
    (pos := .imm (p.n * 1)) (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
    (A := L.rnd) (l := p.n) hc₁.pRnd rfl (by omega)
    (Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hc₁.rd, ← hn]; simp))
    (by rw [← hn]; exact hL.sRnd.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    (by rw [← hn]; exact hL.sRnd.symm.sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    (by rw [← hn]; exact k16 hL.kRnd) hR₁
    (by simp only [argV, List.nil_append, bytesAt_length', Nat.mul_one]; rw [Nat.mod_eq_of_lt (by omega)])
    fun t₂ hc₂ hR₂ hx₂ hf₂ mx₂ => ?_)
  have hsig : Region.Sub ⟨L.sig, p.n⟩ L.SIG := Region.sub_prefix (by rw [← hn]; exact hL.sigN)
  refine tail_ok hL hc₂ hst (pre := [] ++ bytesAt t₀.mem (at' L.S Layout.oSkPrf) p.n ++ bytesAt t₁.mem L.rnd p.n)
    (by simp only [List.length_append, List.length_nil, bytesAt_length']; omega) hR₂
    (by simp only [List.length_append, List.length_nil, bytesAt_length']; omega)
    (dst := .slot Impl.SlhDsa.X86_64.Shake.fSig) (by dsimp only [ArgOk]; decide) (by omega)
    (fun t' hc' => hc'.pSig)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SIG, by rw [hc₂.wr]; simp, 0, by simp, by show 0 + p.n ≤ L.sigL; rw [← hn]; have := hL.sigN; omega⟩)
    ((hL.sSig.sub_right hsig).sub_left (hL.scr_sub (by rw [oStream_eq]; omega)))
    ((hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    ((k16 hL.kSig).sub_right hsig) (.inr (.inr hsig)) fun t' hc' ho hf mx => k t' hc' ?_ ?_
      (mx₀.trans (mx₁.trans (mx₂.trans mx)))
  · have k1 := hc₀.keys 1 (by decide)
    rw [hn, show Layout.oKeys + 32 * 1 = Layout.oSkPrf from rfl] at k1
    rw [ho, k1, hc₁.bytesAt_eq (by rw [← hn]; exact hL.sRnd) (by rw [← hn]; exact hL.kRnd)
      (by rw [← hn]; exact hL.gRnd) (by omega), List.nil_append]
  · exact (hf₀.sub (sub_st L _)).trans ((hf₁.sub (sub_call L _)).trans ((hf₂.sub (sub_call L _)).trans hf))

include hL hc in
/-- The digest `H_msg(R, PK.seed, PK.root, M′)` to `oDigest`, `R` the
signature's first `n` bytes. -/
theorem hashD_ok {p : Spec.SlhDsa.Params} (hn : L.n = p.n) (hm : p.m ≤ 64) (hst : 8 ≤ L.st) {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' →
      bytesAt t'.mem (at' L.S Layout.oDigest) p.m = Spec.Sha3.shake256 (bytesAt t.mem L.sig p.n ++
        bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 2)) p.n ++ bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 3)) p.n ++
        Mp L m₀) p.m →
      Frame [sAll L, ⟨at' L.S Layout.oDigest, p.m⟩, below L.SP 16] t.mem t'.mem → MxEq t t' → Q t') :
    WP isa (Impl.SlhDsa.X86_64.Shake.hashM' p [.slot Impl.SlhDsa.X86_64.Shake.fSig, .scr Layout.oPkSeed,
      .scr Layout.oPkRoot] (.scr Layout.oDigest) p.m) t Q := by
  have hn32 := hL.n32
  rw [hn] at hn32
  have hnB := hL.nB
  have eP : Layout.oPkSeed = 3232 := rfl
  have eR : Layout.oPkRoot = 3264 := rfl
  have eD : Layout.oDigest = 30304 := rfl
  simp only [Impl.SlhDsa.X86_64.Shake.hashM', List.zipIdx_cons, List.zipIdx_nil, List.foldr_cons, List.foldr_nil,
    List.length_cons, List.length_nil]
  have k16 : ∀ {r : Region}, L.STK.Disjoint r → Region.Disjoint (below L.SP 16) r := fun h =>
    h.sub_left fun a ha => hL.cs_stk a (SL.Ok.below_cs L (by omega) hL a ha)
  have hsig : Region.Sub ⟨L.sig, p.n⟩ L.SIG := Region.sub_prefix (by rw [← hn]; exact hL.sigN)
  refine WP.seq (zero_ok hL hc fun t₀ hc₀ hz hf₀ mx₀ => ?_)
  have hR₀ : Repr t₀.mem (at' L.S Layout.oStream) 136 [] := by
    show stateAt t₀.mem _ = Proof.Sha3.Rep 136 []
    rw [Proof.Sha3.rep_nil, hz]
  have hb₀ : bytesAt t₀.mem L.sig p.n = bytesAt t.mem L.sig p.n :=
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega))) (by omega)
  -- `R`
  refine WP.seq (kabs_ok hL hc₀ hst (src := .slot Impl.SlhDsa.X86_64.Shake.fSig) (len := .imm p.n)
    (pos := .imm (p.n * 0)) (by dsimp only [ArgOk]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
    (A := L.sig) (l := p.n) hc₀.pSig rfl (by omega)
    (Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SIG, by rw [hc₀.wr]; simp, 0, by simp, by show 0 + p.n ≤ L.sigL; rw [← hn]; have := hL.sigN; omega⟩))
    ((hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    ((hL.sSig.symm.sub_left hsig).sub_right (hL.scr_sub (by rw [oStream_eq]; omega)))
    ((k16 hL.kSig).sub_right hsig) hR₀ (by simp [argV]) fun t₁ hc₁ hR₁ hx₁ hf₁ mx₁ => ?_)
  -- `PK.seed`
  refine WP.seq (kabs_ok hL hc₁ hst (src := .scr Layout.oPkSeed) (len := .imm p.n) (pos := .imm (p.n * 1))
    (by show _ < 2 ^ 31; rw [eP]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
    (A := at' L.S Layout.oPkSeed) (l := p.n) rfl rfl (by omega)
    (Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc₁.wr]; simp, Layout.oPkSeed, rfl, by show _ + p.n ≤ 65536; rw [eP]; omega⟩))
    (Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega))
    (Levels.disj_scr L.S (by rw [eP, oStream_eq]; omega) (by rw [eP]; omega) (by rw [oStream_eq]; omega))
    ((hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eP]; omega)))
    hR₁ (by simp only [argV, List.nil_append, bytesAt_length', Nat.mul_one]; rw [Nat.mod_eq_of_lt (by omega)])
    fun t₂ hc₂ hR₂ hx₂ hf₂ mx₂ => ?_)
  -- `PK.root`
  refine WP.seq (kabs_ok hL hc₂ hst (src := .scr Layout.oPkRoot) (len := .imm p.n) (pos := .imm (p.n * 2))
    (by show _ < 2 ^ 31; rw [eR]; decide) (by show _ < 2 ^ 31; omega) (by show _ < 2 ^ 31; omega)
    (A := at' L.S Layout.oPkRoot) (l := p.n) rfl rfl (by omega)
    (Covers.right (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc₂.wr]; simp, Layout.oPkRoot, rfl, by show _ + p.n ≤ 65536; rw [eR]; omega⟩))
    (Levels.disj_scr L.S (by rw [eR, oStream_eq]; omega) (by rw [eR]; omega) (by rw [oStream_eq]; omega))
    (Levels.disj_scr L.S (by rw [eR, oStream_eq]; omega) (by rw [eR]; omega) (by rw [oStream_eq]; omega))
    ((hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eR]; omega)))
    hR₂ (by simp only [argV, List.nil_append, List.length_append, bytesAt_length']; rw [Nat.mod_eq_of_lt (by omega)]; congr 1; omega)
    fun t₃ hc₃ hR₃ hx₃ hf₃ mx₃ => ?_)
  refine tail_ok hL hc₃ hst (pre := [] ++ bytesAt t₀.mem L.sig p.n ++ bytesAt t₁.mem (at' L.S Layout.oPkSeed) p.n ++
      bytesAt t₂.mem (at' L.S Layout.oPkRoot) p.n)
    (by simp only [List.length_append, List.length_nil, bytesAt_length']; omega) hR₃
    (by simp only [List.length_append, List.length_nil, bytesAt_length']; omega)
    (dst := .scr Layout.oDigest) (by show _ < 2 ^ 31; rw [eD]; decide) (by omega) (D := at' L.S Layout.oDigest)
    (fun _ _ => rfl)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by rw [hc₃.wr]; simp, Layout.oDigest, rfl, by show _ + p.m ≤ 65536; rw [eD]; omega⟩)
    (Levels.disj_scr L.S (by rw [eD, oStream_eq]; omega) (by rw [oStream_eq]; omega) (by rw [eD]; omega))
    (Levels.disj_scr L.S (by rw [eD, oStream_eq]; omega) (by rw [eD]; omega) (by rw [oStream_eq]; omega))
    ((hL.cs_scr.sub_left (SL.Ok.below_cs L (by omega) hL)).sub_right (hL.scr_sub (by rw [eD]; omega)))
    (free_hi hL (by decide) (by rw [eD]; omega) (.inl (by rw [eD]; show _ ≤ 34080; omega))) fun t' hc' ho hf mx =>
      k t' hc' ?_ ?_ (mx₀.trans (mx₁.trans (mx₂.trans (mx₃.trans mx))))
  · have k2 := hc₁.keys 2 (by decide)
    have k3 := hc₂.keys 3 (by decide)
    rw [hn, show Layout.oKeys + 32 * 2 = Layout.oPkSeed from rfl] at k2
    rw [hn, show Layout.oKeys + 32 * 3 = Layout.oPkRoot from rfl] at k3
    rw [ho, k2, k3, hb₀, List.nil_append]
  · exact (hf₀.sub (sub_st L _)).trans ((hf₁.sub (sub_call L _)).trans ((hf₂.sub (sub_call L _)).trans
      ((hf₃.sub (sub_call L _)).trans hf)))

end

end VG.Proof.SlhDsa.X86_64.SignTop
