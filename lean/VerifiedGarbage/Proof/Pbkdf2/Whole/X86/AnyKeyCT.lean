module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKey
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Md5.X86.Lit
public import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# HMAC's `init` for a key of any length on x86 (32-bit): constant time, and the shared contract

As for `pbkdf2` (`CT.lean`): the pieces of code between the calls are checked
by the taint analysis (`AnyChecks`, which the kernel evaluates for each hash
function), with the arguments, `esp` and `ebp` public (`piece`); the calls are
related by their contracts (`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`), whose
public arguments are the same in two runs with the same public arguments
(`PubEq`). The only branch, whether the key is hashed, depends only on
`key_len`.

`anyG` (the arguments writable, as the shared contract has them) follows from
`anyN` (`Verified.narrowTo`), and implies `anyScratchContract`:
`VG.Spec.Hmac.initAnyKeyContract` with its working space as a last argument,
from which the function that allocates it in a frame of its own and wipes it
(`withStackScratchWiped`) is verified (`anyFramed`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86.Any

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Whole.X86 (FnsOK Sizes layout end_le hi_rel hash_len blockKey_hash shapeOf setWidth_inj32)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel upd_rel fin_rel)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash blockKey xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs (4 + 4 * 5)) c hc).isSome = true

/-- The taint checks of the pieces of `initAny` between its calls. -/
structure AnyChecks (F : Fns) : Prop where
  pro : Ck [] (.block F.anyPrologue)
  cmp : Ck [.ebp] (.block F.anyCmp)
  hk1 : Ck [.ebp] (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO))
  hk3 : Ck [.ebp] (.block Fns.anyHk3)
  hk5 : Ck [.ebp] (.block F.anyHk5)
  hk7 : Ck [.ebp]
    (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++ ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr)))
  short : Ck [.ebp] (.block Fns.anyShort)
  args : Ck [.ebp] (.block Fns.anyArgs)
  restore : Ck [.ebp] (.block F.L.restore)

/-- The checks depend only on the sizes of `F`. -/
theorem anyChecks_of_shape {F : Fns} (h : AnyChecks (shapeOf F)) : AnyChecks F :=
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.args, h.restore⟩

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : E s₀ = E s₀'
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 5) : arg s₀' i = arg s₀ i := (hq.args i hi).symm
theorem PubEq.E' : E s₀' = E s₀ := hq.esp.symm
theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a (by decide)
theorem PubEq.innEq : inn s₀' = inn s₀ := hq.a (by decide)
theorem PubEq.outEq : out s₀' = out s₀ := hq.a (by decide)
theorem PubEq.keyEq : key s₀' = key s₀ := hq.a (by decide)
theorem PubEq.klnEq : kln s₀' = kln s₀ := by show (arg s₀' 3).toNat = _; rw [hq.a (by decide)]
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by show scr s₀' + _ = _; rw [hq.scrEq]
theorem PubEq.kpEq : kp F s₀' = kp F s₀ := by
  show (if kln s₀' < F.H.B + 1 then arg s₀' 2 else dO s₀' F.hkO) = _
  rw [hq.klnEq, hq.a (by decide), hq.dOEq]
theorem PubEq.klEq : kl F s₀' = kl F s₀ := by
  show (if kln s₀' < F.H.B + 1 then kln s₀' else F.H.D) = _
  rw [hq.klnEq]

end

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_i h.i_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_o h.o_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree_argTaint (hag s s' h h')
      (by rw [(hk h).esp, (hk h').esp, hq.esp])
      (args_out hp (hk h).esp (hk h).wr) (args_out hp' (hk h').esp (hk h').wr)
      fun i hi => by rw [(hk h).argEq hp hi, (hk h').argEq hp' hi, hq.args i hi]) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_ebp {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, hq.scrEq]

end

/-! ## The key -/

/-- The key is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ kln t₀

/-- The pieces of hashing the key: the state for its digest, then `update`
with the key, then `finalize`. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = arg t₀ 3 ∧
    s.gpr .edx = key t₀ ∧ hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀)) ∧
    s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .eax = arg t₀ 3 ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = dO t₀ F.hkO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem ((key t₀).setWidth 64) (kln t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ s.gpr .ecx = arg t₀ 3 ∧ s.cf = some (decide (kln t₀ < F.H.B + 1))

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : AnyChecks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KR F s₀ s ∧ Long F s₀) ∧ (KR F s₀' s' ∧ Long F s₀')) F.anyHashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  unfold Fns.anyHashKey
  have r1 := piece hp hp' hq (fun t₀ s => KR F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1)
    (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2 : RelCT isa (fun s s' => Hk1 F s₀ s ∧ Hk1 F s₀' s') (F.H.callInit .edi)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (sp := E s₀) (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, d⟩, _⟩, ⟨⟨k', d'⟩, _⟩⟩ =>
        ⟨hk2_args hp hz k d, by have := hk2_args hp' hz k' d'; rwa [hq.dOEq] at this, k.esp,
          by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp' hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok hp₀ k d) fun t ⟨k', d', i, a, c, x, m⟩ =>
      ⟨⟨k', d', i, a, c, x, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x, _⟩, _⟩, ⟨⟨k', d', i', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k d i a c x,
          by have := hk4_args hp' hz hF.hH k' d' i' a' c' x'; rwa [hq.dOEq, hq.keyEq, hq.scrEq,
            hq.klnEq] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk5
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk5_ok hp₀ k d) fun t ⟨k', d', a, c, x, m⟩ =>
      ⟨⟨k', d', a, c, x, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, a, c, x, _⟩, _⟩, ⟨⟨k', d', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k d a c x,
          by have := hk6_args hp' hz hF.hH k' d' a' c' x'; rwa [hq.dOEq, hq.dOEq, hq.scrEq,
            show arg s₀' 3 = arg s₀ 3 from hq.a (by decide)] at this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1)
    hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ kln t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (hz.hkO_lt), m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega)
        (hash_len hF.hH b)])
  exact r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))

theorem key_rel :
    RelCT isa (fun s s' => KR F s₀ s ∧ KR F s₀' s') F.anyKey fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.anyKey
  have rc := piece hp hp' hq (fun t₀ s => KR F t₀ s) (Cmp F) id (fun s s' h h' => ag_ebp hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hp₀ hz k) fun t ⟨k', c, f, _⟩ => ⟨k', c, f⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .ae t = some (decide (F.H.B + 1 ≤ kln t₀)) := by
    intro t₀ t h
    show t.cf.map (!·) = _
    rw [h.2.2]; simp only [Option.map_some, ← decide_not, Nat.not_lt]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.klnEq]) ?_ ?_)
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, this⟩, h.1.2.1, by show F.H.B + 1 ≤ kln s₀'; rw [hq.klnEq]; exact this⟩
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ kln t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1)
      (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, c, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = key t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = kln t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine wp_arg hp₀ k (by decide) fun s₂ u₂ => WP.block_nil ⟨k.upd (by decide) u₂, by rw [u₂.gpr, ekp], ?_, ?_⟩
      · rw [u₂.other _ (by decide), c, ekl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [u₂.mem, ekp, ekl, k.keyBytes hp₀]
    · have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      have hlt : kln s₀ < F.H.B + 1 := by omega
      exact ⟨⟨h.1.1, hlt⟩, h.1.2, by rw [hq.klnEq]; exact hlt⟩

/-- After `anyArgs`. -/
abbrev Ag (hF : FnsOK F) (t₀ t : State) : Prop := Keyed hF t₀ t ∧ t.gpr .edi = inn t₀ ∧ t.gpr .esi = out t₀

/-- After HMAC's `init`. -/
abbrev Done (hF : FnsOK F) (t₀ t : State) : Prop :=
  KR F t₀ t ∧ hF.hH.SH.Repr t.mem ((inn t₀).setWidth 64) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr t.mem ((out t₀).setWidth 64) (xorPad (K0 hF t₀) opad)

include hF in
/-- `initAny` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.hmacInitAny fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KR F s₀) (G' := KR F s₀')
    (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have ra := piece hp hp' hq (Keyed hF) (Ag hF) (fun h => h.kr) (fun s s' h h' => ag_ebp hq h.kr h'.kr) hc.args
    (fun hp₀ s h => args_ok hp₀ hF h)
  have rc : RelCT isa (fun s s' => Ag hF s₀ s ∧ Ag hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
      fun s s' => Done hF s₀ s ∧ Done hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := E s₀) fun s s' ⟨⟨h, d, i⟩, ⟨h', d', i'⟩⟩ =>
        ⟨call_args hp hz hF h d i,
          by have := call_args hp' hz hF h' d' i'; rwa [hq.innEq, hq.outEq, hq.kpEq, hq.scrEq, hq.klEq] at this,
          h.kr.esp, by rw [h'.kr.esp, hq.E']⟩)
      (fun s ⟨h, d, i⟩ => call_ok hp hz hF h d i) (fun s ⟨h, d, i⟩ => call_ok hp' hz hF h d i)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Done hF s₀ s ∧ Done hF s₀' s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint [.ebp] (4 + 4 * 5)) (fun s s' h => agree_argTaint (ag_ebp hq h.1.1 h.2.1)
      (by rw [h.1.1.esp, h.2.1.esp, hq.esp]) (args_out hp h.1.1.esp h.1.1.wr) (args_out hp' h.2.1.esp h.2.1.wr)
      fun i hi => by rw [h.1.1.argEq hp hi, h.2.1.argEq hp' hi, hq.args i hi]) hr
  unfold Fns.hmacInitAny
  exact pro.seq ((key_rel hp hp' hq hc).seq (ra.seq (rc.seq restore)))

end

/-- `initAny` is verified against `anyN`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verifiedN (hF : FnsOK F) (hc : AnyChecks F) (hsat : ∃ s, (anyN hF.hH.SH (F.W + F.H.S)).pre s) :
    Verified X86.target F.hmacInitAny (anyN hF.hH.SH (F.W + F.H.S)) := by
  refine ⟨fun s hs => correct (pre_of hF hs) hF.sizes hF, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) ⟨h1, h2⟩ hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The shared contract -/

variable (S : StreamingHash) (W : Nat)

/-- `anyN` with the arguments writable, as the shared contract has them. -/
def anyG : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint key ∧ inner.Disjoint scratch ∧ inner.Disjoint args ∧
    outer.Disjoint key ∧ outer.Disjoint scratch ∧ outer.Disjoint args ∧ key.Disjoint scratch ∧
    key.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint key ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + W * 8 ≤ 2 ^ 32
  post := (anyN S W).post
  pub := (anyN S W).pub

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s), and
76 bytes of stack: the contract that the function allocating the working
space follows from (`Verified.stackScratchWiped`). -/
def anyScratchContract : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract X86.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S X86.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 76)

/-- `anyG` implies the shared contract for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem anyImp (h : ∃ s, (anyScratchContract S W).pre s) : (anyG S W).Implies (anyScratchContract S W) := by
  exact
    { pre := by
        intro s h
        sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi] at h
        simp only [argVal32, toNat_setWidth64, show argBytes [32, 32, 32, 32, 32] = 20 from rfl] at h
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27⟩ := h
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27⟩
      post := by
        rintro s s' - h
        sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, a0, a1, a2, a3, a4⟩ := h
        refine ⟨e, fun i hi => ?_⟩
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
        · exact setWidth_inj32 a0
        · exact setWidth_inj32 a1
        · exact setWidth_inj32 a2
        · exact setWidth_inj32 a3
        · exact setWidth_inj32 a4
      sat := h }

/-- The regions the proof gives `initAny`: the arguments readable. -/
def narrowRd (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S W : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 1).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, W * 8⟩]

/-- A state for `anyG`, given the regions `anyN` gives. -/
theorem anyN_pre {s : State} (h : (anyG S W).pre s) :
    (anyN S W).pre (s.withRegions (narrowRd s) (narrowWr S.stateBytes W s)) := by
  obtain ⟨h0, h1, _, _, h4, h5, h6, h7, h8, h9, h10, h11, _, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27⟩ := h
  simp only [anyN, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨h0, h1, trivial, trivial, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27⟩

/-- Verified against `anyN`, so against `anyG`. -/
theorem verified_anyG {c : Prog isa} (h : Verified X86.target c (anyN S W)) (hsat : ∃ s, (anyG S W).pre s) :
    Verified X86.target c (anyG S W) := by
  refine Verified.narrowTo h narrowRd (narrowWr S.stateBytes W) (fun s h => anyN_pre S W h) (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, _, h2, h3, _⟩ := h
    rw [h2, h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨_, _, _, h3, _⟩ := h
    rw [h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp

/-- `initAny` is verified against the shared contract, given the taint checks
and a state satisfying the shared contract. -/
theorem verified (hF : FnsOK F) (hc : AnyChecks F) {S : StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (anyScratchContract S W).pre s) :
    Verified X86.target F.hmacInitAny (anyScratchContract S W) := by
  subst hS hW
  have imp := anyImp hF.hH.SH (F.W + F.H.S) hsat
  have gsat : ∃ s, (anyG hF.hH.SH (F.W + F.H.S)).pre s := hsat.elim fun s h => ⟨s, imp.pre s h⟩
  exact (verified_anyG _ _ (verifiedN hF hc (gsat.elim fun s h => ⟨_, anyN_pre _ _ h⟩)) gsat).of_implies imp

/-! ## Its stack, and `esp` -/

/-- `initAny` uses at most 76 bytes of stack. -/
theorem hmacInitAny_stack (hF : FnsOK F) : stackUse F.hmacInitAny ≤ 76 := by
  have := hF.hH.initSU; have := hF.hH.updSU; have := hF.hH.finSU; have := hF.hiSU
  simp only [Fns.hmacInitAny, Fns.anyKey, Fns.anyHashKey, Impl.Pbkdf2.Stream.X86.Hash.callInit,
    stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at *
  omega

/-- `initAny`'s instructions all satisfy `p` if those of the functions it
calls do and those of its own pieces do (`shapeOf`, decided for each hash
function). -/
theorem hmacInitAny_allInstrs {p : Instr → Bool} (hb : (shapeOf F).hmacInitAny.allInstrs p = true)
    (hi : F.H.initC.allInstrs p = true) (hu : F.H.updC.allInstrs p = true) (hf : F.H.finC.allInstrs p = true)
    (hh : F.hiC.allInstrs p = true) : F.hmacInitAny.allInstrs p = true := by
  have e1 : (shapeOf F).H.initC = .block [] := rfl
  have e2 : (shapeOf F).H.updC = .block [] := rfl
  have e3 : (shapeOf F).H.finC = .block [] := rfl
  have e4 : (shapeOf F).hiC = .block [] := rfl
  simp only [Fns.hmacInitAny, Fns.anyKey, Fns.anyHashKey, Impl.Pbkdf2.Stream.X86.Hash.callInit, Code.allInstrs,
    e1, e2, e3, e4, hi, hu, hf, hh, Bool.and_true] at hb ⊢
  exact hb

theorem allInstrs_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp [h i hi]

theorem all_writesSp_eq (c : Prog isa) :
    c.all (fun i => !isa.writesSp i) = c.allInstrs (fun i => !Taint.clobbers i .esp) := by
  rw [Whole.X86.all_eq, Code.allInstrs_eq]
  simp only [Whole.X86.clobbers_esp]

/-- `initAny` writes `esp` only through its frames' pushes and pops. -/
theorem hmacInitAny_noEsp (hF : FnsOK F)
    (hb : (shapeOf F).hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true) :
    F.hmacInitAny.allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  hmacInitAny_allInstrs hb (allInstrs_of_noSp hF.hH.initSp) (allInstrs_of_noSp hF.hH.updSp)
    (allInstrs_of_noSp hF.hH.finSp) (allInstrs_of_noSp hF.hiSp)

/-! ## In a frame of its own, wiped -/

/-- The bytes of `init`'s frame: its return address, a copy of its four
argument slots and the working space. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := 8 + 16 + 8 * I.initAnyKeyScratch

/-- `initAny` in a frame holding its working space, which it wipes before
returning: verified against `initAnyKeyContract`, from the locality of its
postcondition (`Proof/Hmac/AnyKey.lean`). -/
theorem anyFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (anyScratchContract I.S I.initAnyKeyScratch))
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.initAnyKeyContract X86.abi (76 + anyFrame I)).pre s)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true)
    (hd : stackUse c ≤ 76) (hs : 8 * I.initAnyKeyScratch < 4072 := by decide) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped (anyFrame I) 4 (2 * I.initAnyKeyScratch) c)
      (I.initAnyKeyContract X86.abi (76 + anyFrame I)) :=
  X86.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S X86.abi.ptrBits) (wa := true) (stack := 76)
    (bytes := anyFrame I) (words := 2 * I.initAnyKeyScratch) h
    (by
      refine ⟨?_, by simp only [anyFrame]; omega, by simp only [anyFrame]; omega⟩
      change 8 + 4 * 4 + I.initAnyKeyScratch * 8 ≤ anyFrame I
      simp only [anyFrame]; omega)
    hsp hd (by change 4 * (2 * I.initAnyKeyScratch) ≤ I.initAnyKeyScratch * 8; omega)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.initPost_local I.S _) (Hmac.initPostOut_local I.S _ hR hS) hsat rfl

/-- The frame of `withStackScratchWiped` keeps the stack pointer for any `c`
that does, if it does for an empty body and its wipe (decided for literal
sizes). -/
theorem withStackScratchWiped_spSafe {bytes n words : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true)
    (hw : (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * n) words) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by decide +kernel)
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide +kernel) :
    (Impl.StackScratch.X86.withStackScratchWiped bytes n words c).all (fun i => !isa.writesSp i) = true :=
  Md.X86.withStackScratch_spSafe (c := .seq c (.block _)) (by simp only [Code.all, h, Bool.true_and]; exact hw) hf

end VG.Proof.Pbkdf2.Whole.X86.Any
