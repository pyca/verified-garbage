module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFixed
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSASSA-PSS signing on x86-64, around the encoding: constant time, and
`Verified`

The prologue and the check of the modulus' first byte (`spro_ct`), `emBits`
and `encode`'s arguments (public: the modulus' length and first byte, and
places), the call of `encode` (constant time by its contract: its public
data, the places and lengths, agree), whose result is public (whether the
salt fits, `encode_isSome`), the private-key operation's arguments and call
(`scall_ct`), and the epilogue, in two runs whose entry states agree on the
public data (`signC_ct`). With `signC_correct`, `signC` meets
`Spec.RsaPss.signContract` (`signC_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {G : Spec.Mgf1.Hash} {H : Hash}

/-! ## The public values -/

/-- `emBits`. -/
def seb (s : State) : Nat := ebV (s.gpr .rcx).toNat (sn0v s)

/-- `emLen`. -/
def sel (s : State) : Nat := Spec.RsaPss.emLength (seb s)

/-- `lo`. -/
def sclo (s : State) : Nat := (s.gpr .rcx).toNat - sel s

variable (G) in
/-- Whether the encoding fits. -/
def sfits (s : State) : Prop := G.len + ssl s + 2 ≤ sel s

instance (s : State) : Decidable (sfits G s) := inferInstanceAs (Decidable (_ ≤ _))

theorem SSib.seb {a s : State} (S : SSib G a s) : seb s = seb a := by
  simp only [VG.Proof.RsaPss.X86_64.seb, S.sn0v, S.gpr (r := .rcx) (by decide)]

theorem SSib.sel {a s : State} (S : SSib G a s) : sel s = sel a := by
  simp only [VG.Proof.RsaPss.X86_64.sel, S.seb]

theorem SSib.sclo {a s : State} (S : SSib G a s) : sclo s = sclo a := by
  simp only [VG.Proof.RsaPss.X86_64.sclo, S.sel, S.gpr (r := .rcx) (by decide)]

theorem SSib.sfits {a s : State} (S : SSib G a s) : sfits G s ↔ sfits G a := by
  simp only [VG.Proof.RsaPss.X86_64.sfits, S.sel, S.ssl]

theorem seb_ok {s : State} (hp : SPre G s) :
    sclo s ≤ 1 ∧ 1 ≤ seb s ∧ seb s ≤ Proof.RsaPss.maxEmBits ∧ sel s ≤ 1024 := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hl8 : Nat.log2 (sn0v s) < 8 := RsaPss.log2_lt8 (s.mem (s.gpr .rdx))
  refine ⟨lo_le hl8 (by omega_arith), ?_, ?_, ?_⟩
  · unfold seb ebV; omega_arith
  · unfold seb ebV Proof.RsaPss.maxEmBits; omega_arith
  · unfold sel seb ebV Spec.RsaPss.emLength; omega_arith

/-- `encode`'s result, from whether it fits. -/
theorem rax_of {e : Option (List Byte)} {x : BitVec 64} {c : Bool} {P : List Byte → Prop}
    (h : match e with | some e' => x.setWidth 32 = 1 ∧ P e' | none => x.setWidth 32 = 0) (hc : e.isSome = c) :
    x.setWidth 32 = if c then 1 else 0 := by
  cases e with
  | none => subst hc; exact h
  | some e' => subst hc; exact h.1

/-! ## The pieces -/

/-- After the frame's push. -/
def J0 (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def KS1 : List Nat := [16, 17, 18, 19, 20, 21, 22, 37, 39, 40]

variable (H) in
/-- After the prologue: the modulus' first byte, and ZF set if it is zero. -/
def SJ1 (s t : State) : Prop :=
  SS H s t KS1 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (sn0v s) ∧ t.zf = some (decide (sn0v s = 0))

variable (H) in
/-- At the end. -/
def SJR (s t : State) : Prop := SS H s t [] [] fun _ _ => True

theorem spro_ct : RelCT isa (Two (SAt G J0)) (.block (signPrologue ++ n0)) (Two (SAt G (SJ1 H))) := by
  obtain ⟨_, hc⟩ := sFixed.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 2 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff]
  refine WP.mono (signPro_ok hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  refine WP.mono (n0_ok hp L1 R1 (by simp [proW, upd]) k1.2.1 (frame_wrR f1)) fun t2 ⟨k2, hm2, hax2, hz2⟩ =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k2.2.1.trans k1.2.1,
      hm2 ▸ frame_wrR f1, hax2, hz2⟩
  simp only [KS1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [proW, upd, sw]

/-- A refusal: zeros to `out`. -/
theorem sfail_ct {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s X, SSib G a s ∧ SS H s t [16, 17] [] X) :
    RelCT isa (Two Φ) signFail (Two (SAt G (SJR H))) := by
  obtain ⟨_, hc⟩ := sFixed.fail
  refine two_post (stwo (G := G) (H := H) [16, 17] [] (fun _ => []) hΦ (fun _ => rfl) (by decide) hc)
    fun a t h => ?_
  obtain ⟨s, X, S, v⟩ := hΦ a t h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [v.wr, hp.hwr, ← hp.hsi]; simp
  have hO : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (stkR s) := by rw [← hp.hsi]; exact hp.dKo.symm
  exact WP.mono (signFail_ok v.L R (out := s.gpr .rdi) (k := (s.gpr .rcx).toNat) (hw 16 (by decide))
    (by rw [hw 17 (by decide)]; show s.gpr .rcx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_arith) hk2
    hout (by rw [← hp.hsi]; exact hp.wO)
    ((by rw [← hp.hsi]; exact hp.dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint
      ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩).sub_right (Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_arith)))
    (hO.sub_right (frame_sub s))) fun u ⟨L', k', R', _⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial⟩

variable (H) in
/-- Before the call. -/
def SJP (s t : State) : Prop :=
  SS H s t [] [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i) ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

/-- The words the private-key operation's arguments read. -/
def KSP : List Nat := [16, 17, 18, 19, 20, 22]

variable (H) in
/-- Before `encode`. -/
def CJE (s t : State) : Prop :=
  SS H s t KSP [] (fun _ W => W 0 = off (stackArg s 13) oEnc ∧ W 1 = stackArg s 14 - BitVec.ofNat 64 (oEnc / 8)) ∧
    t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧ sn0v s ≠ 0 ∧
    t.gpr .rdi = off (stackArg s 13) (oEm + sclo s) ∧ t.gpr .rsi = BitVec.ofNat 64 (sel s) ∧
    t.gpr .rdx = stackArg s 10 ∧ t.gpr .rcx = stackArg s 11 ∧ t.gpr .r8 = stackArg s 12 ∧
    t.gpr .r9 = BitVec.ofNat 64 (seb s)

variable (G H) in
/-- After `encode`. -/
def CJC (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    (t.gpr .rax).setWidth 32 = if decide (sfits G s) then 1 else 0

variable (G H) in
/-- After the test. -/
def CJT (s t : State) : Prop :=
  SS H s t KSP [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.zf = some (!decide (sfits G s))

theorem cprep_ct :
    RelCT isa (Two fun a t => SAt G (SJ1 H) a t ∧ isa.eval .e t = some false) (.block (emBitsB ++ encArgs))
      (Two (SAt G (CJE H))) := by
  obtain ⟨_, hc⟩ := scFixed.prep
  refine two_post (stwo (G := G) (H := H) [17, 21, 22, 37, 39, 40] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (sn0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.sn0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have h0 : sn0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (encPrep_ok v.L R (hw 17 (by decide)) (hw 22 (by decide)) (hw 37 (by decide)) (hw 39 (by decide))
      (hw 40 (by decide)) (by omega_arith) hk2 (x := sn0v s) (BitVec.isLt _) h0 hax))
    fun u ⟨⟨L', k', R', di, si, dx, cx, r8, r9⟩, f⟩ =>
      ⟨s, S, v.next L' k'.2.2 R' (fun k hk => ?_) ⟨by simp [encW, upd], by simp [encW, upd]⟩, k'.2.1.trans hrd,
        frame_keep hp v.wr v.L.rsp hM f, h0, di, si, dx, cx, r8, r9⟩
  simp only [KSP, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hk' : k ∈ KS1 := by simp only [KS1, List.mem_cons, List.not_mem_nil, or_false]; omega_arith
  simp only [encW, upd]
  rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  exact hw k hk'

variable {encN : String} {encC : Prog isa}
  (hvE : ∀ s, (encK G).pre s → ∃ t s', Exec isa encC s t s' ∧ abiPreserved s s' ∧ (encK G).post s s')
  (hctE : ConstantTime isa (encK G).pre (encK G).pub encC) (hspE : SpSafe encC)
  (hdE : encC.x86_64Depth ≤ encStack)

include hvE hctE hspE hdE in
theorem ecall_ct : RelCT isa (Two (SAt G (CJE H))) (.call encN encC) (Two (SAt G (CJC G H))) := by
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp →
      (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine two_post (RelCT.callEx (k := encK G) hvE hctE fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨v₁, rd₁, -, n₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, rd₂, -, n₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    obtain ⟨V₁, W₁, R₁, -, x₁, y₁⟩ := v₁.W
    obtain ⟨V₂, W₂, R₂, -, x₂, y₂⟩ := v₂.W
    have p₁ := S₁.ps; have p₂ := S₂.ps
    obtain ⟨lo₁, e₁, f₁, l₁⟩ := seb_ok p₁
    obtain ⟨lo₂, e₂, f₂, l₂⟩ := seb_ok p₂
    obtain ⟨c₁, w₁⟩ := enc_covers p₁ rd₁ v₁.wr lo₁ l₁
    obtain ⟨c₂, w₂⟩ := enc_covers p₂ rd₂ v₂.wr lo₂ l₂
    have a₀₁ := (R₁.fr 0 (by decide)).trans x₁
    have a₁₁ := (R₁.fr 1 (by decide)).trans y₁
    have a₀₂ := (R₂.fr 0 (by decide)).trans x₂
    have a₁₂ := (R₂.fr 1 (by decide)).trans y₂
    refine ⟨_, _, _, _, enc_pre p₁ v₁.L.rsp a₀₁ a₁₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ lo₁ e₁ f₁ rfl,
      enc_pre p₂ v₂.L.rsp a₀₂ a₁₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ lo₂ e₂ f₂ rfl, ⟨fun r hr => ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂,
      by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.arg (i := 13) (by decide),
          S₂.arg (i := 13) (by decide), S₁.sclo, S₂.sclo]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.sel, S₂.sel]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.arg (i := 10) (by decide),
          S₂.arg (i := 10) (by decide)]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.arg (i := 11) (by decide),
          S₂.arg (i := 11) (by decide)]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.arg (i := 12) (by decide),
          S₂.arg (i := 12) (by decide)]
      · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.seb, S₂.seb]
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
          v₂.L.rsp, S₁.fb, S₂.fb]
    · rw [stackArg_call p₁ v₁.L.rsp _ _ (i := 0) (by decide), stackArg_call p₂ v₂.L.rsp _ _ (i := 0) (by decide),
        a₀₁, a₀₂, S₁.arg (i := 13) (by decide), S₂.arg (i := 13) (by decide)]
    · rw [stackArg_call p₁ v₁.L.rsp _ _ (i := 1) (by decide), stackArg_call p₂ v₂.L.rsp _ _ (i := 1) (by decide),
        a₁₁, a₁₂, S₁.arg (i := 14) (by decide), S₂.arg (i := 14) (by decide)]
  · obtain ⟨v, hrd, hM, n0, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, x0, x1⟩ := v.W
    have hp := S.ps
    obtain ⟨lo, e1, e2, -⟩ := seb_ok hp
    refine WP.mono (enc_call hvE hspE hdE hp v.L.rsp hrd v.wr hM R ((R.fr 0 (by decide)).trans x0)
      ((R.fr 1 (by decide)).trans x1) di si dx cx r8 r9 lo e1 e2 rfl)
      fun u ⟨rd', wr', cs', _, hM', R', hE⟩ => ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr'
        R' hw trivial, rd'.trans hrd, hM', rax_of hE ?_⟩
    rw [RsaPss.encode_isSome G (Bignum.bytesAt_length ..), Bignum.bytesAt_length]
    rfl

theorem ctest_ct : RelCT isa (Two (SAt G (CJC G H))) (.block [.alu32 .test .rax (.reg .rax)])
    (Two (SAt G (CJT G H))) := by
  obtain ⟨_, hc⟩ := scFixed.test
  refine two_post (stwo (G := G) (H := H) [] [] (fun _ => [])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hax⟩ := h
  refine WP.mono (test32_ok t) fun u ⟨k, hm, hz⟩ =>
    ⟨s, S, v.keep k hm (by decide) (fun _ hp => by cases hp), k.2.1.trans hrd, hm ▸ hM, ?_⟩
  rw [hz, hax]
  by_cases hf : sfits G s <;> simp [hf]

theorem cpriv_ct : RelCT isa (Two fun a t => SAt G (CJT G H) a t ∧ isa.eval .e t = some false) (.block privArgs)
    (Two (SAt G (SJP H))) := by
  obtain ⟨_, hc⟩ := sFixed.privArgs
  refine two_post (stwo (G := G) (H := H) [] [] (fun _ => [])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, _⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (privArgs_ok hp v.L hrd (argsKept_of hp hM) R (hw 16 (by decide)) (hw 17 (by decide)) (hw 18 (by decide))
      (hw 19 (by decide)) (hw 20 (by decide)) (hw 22 (by decide))))
    fun u ⟨⟨k', L', ⟨W', R', ha, _⟩, di, si, dx, cx, r8, r9⟩, f⟩ =>
    ⟨s, S, v.next L' k'.2.2 R' (fun _ h => by cases h) trivial, k'.2.1.trans hrd, frame_keep hp v.wr v.L.rsp hM f,
      fun i hi => (R'.fr i (by unfold nW frameBytes; omega_arith)).trans (ha i hi), di, si, dx, cx, r8, r9⟩

/-- An input, at the call, as on entry. -/
theorem sentry_bytes {s t : State} (hst : t.gpr .rsp = fb s) (hM : Frame (wrR s) s.mem t.mem)
    {R : Region} (hK : (stkR s).Disjoint R) (hO : (outR s).Disjoint R) (hS : R.Disjoint (scrR s))
    (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  exact bytesAt_frame fSE (in_apart hK hO hS) hl

theorem pArg_sib {a s : State} (S : SSib G a s) {i : Nat} (hi : i < 14) : pArg s i = pArg a i := by
  unfold pArg
  split
  · rw [S.arg (i := 13) (by decide)]
  · rw [S.gpr (r := .rcx) (by decide)]
  · rw [S.arg (i := 13) (by decide)]
  · rw [S.arg (i := 14) (by decide)]
  · exact S.arg (by omega_arith)

/-- The call's public data agree. -/
theorem scall_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : SSib G a s₁) (h₁ : SJP H s₁ t₁) (S₂ : SSib G a s₂)
    (h₂ : SJP H s₂ t₂) :
    chkContract.pub (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 14, stackArg (t₁.callEntry.withRegions (pRd s₁) (pWr s₁)) i = pArg a i :=
    fun i hi => ((stackArg_call p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (pArg_sib S₁ hi)
  have hE₂ : ∀ i < 14, stackArg (t₂.callEntry.withRegions (pRd s₂) (pWr s₂)) i = pArg a i :=
    fun i hi => ((stackArg_call p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (pArg_sib S₂ hi)
  have bn : ∀ {s t : State}, SSib G a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.nB]
    exact sentry_bytes (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hst hM hp.dKn hp.dOn hp.dns
      (by have := hp.wN; dsimp only; omega_arith)
  have be : ∀ {s t : State}, SSib G a s → t.gpr .rsp = fb s → Frame (wrR s) s.mem t.mem →
      Spec.Rsa.bytesAt t.callEntry.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := fun {s t} S hst hM => by
    have hp := S.ps
    rw [← S.eB]
    exact sentry_bytes (R := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩) hst hM hp.dKe hp.dOe hp.des
      (by have := hp.wE; dsimp only; omega_arith)
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.gpr (r := .rdi) (by decide),
        S₂.gpr (r := .rdi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .r8) (by decide),
        S₂.gpr (r := .r8) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .r9) (by decide),
        S₂.gpr (r := .r9) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · have hi := List.mem_range.mp hi
    rw [hE₁ i hi, hE₂ i hi]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn S₁ v₁.L.rsp hM₁, bn S₂ v₂.L.rsp hM₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be S₁ v₁.L.rsp hM₁, be S₂ v₂.L.rsp hM₂]

variable {privN : String} {privC : Prog isa}
  (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
  (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
  (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)

include hv hct hspC hdC in
theorem scall_ct : RelCT isa (Two (SAt G (SJP H))) (.call privN privC) (Two (SAt G (SJR H))) := by
  refine two_post (RelCT.callEx (k := chkContract) hv hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := priv_covers S₁.ps h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := priv_covers S₂.ps h₂.2.1 h₂.1.wr
    have hpub := scall_pub S₁ h₁ S₂ h₂
    obtain ⟨v₁, -, -, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := h₁
    obtain ⟨v₂, -, -, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := h₂
    exact ⟨_, _, _, _, priv_pre S₁.ps v₁.L.rsp ha₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁,
      priv_pre S₂.ps v₂.L.rsp ha₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂, hpub, c₁, w₁, c₂, w₂,
      by rw [v₁.L.rsp, v₂.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.ps
    refine WP.mono (priv_call hv hspC hdC hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ => ?_
    have R' := R.of_keep v.L.geo fun x hx => hk' x hx
    exact ⟨s, S, v.next (v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr') wr' R' hw trivial⟩

theorem srestore_ct : RelCT isa (Two (SAt G (SJR H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := sFixed.restore
  exact stwo (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hvE hctE hspE hdE hv hct hspC hdC in
theorem scbody_ct (H : Hash) : RelCT isa (Two (SAt G J0)) (signCBody encN encC privN privC) fun _ _ => True := by
  unfold signCBody
  simp only [seqs]
  refine (spro_ct (H := H)).seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.sn0v, S₂.sn0v])
    (sfail_ct (Φ := fun a t => SAt G (SJ1 H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
    (cprep_ct.seq ((ecall_ct hvE hctE hspE hdE).seq (ctest_ct.seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2,
            h₂.2.2.2, decide_eq_decide.mpr ((S₁.sfits).trans S₂.sfits.symm)])
        (sfail_ct (Φ := fun a t => SAt G (CJT G H) a t ∧ isa.eval .e t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
        (cpriv_ct.seq (scall_ct hv hct hspC hdC))))))).seq srestore_ct)

include hvE hctE hspE hdE hv hct hspC hdC in
/-- `signC` is constant time. -/
theorem signC_ct (H : Hash) : ConstantTime isa (signK G).pre (signK G).pub (signC encN encC privN privC) :=
  RelCT.constantTime (valloc ((scbody_ct (H := H) hvE hctE hspE hdE hv hct hspC hdC).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, spub_refl G s₁, h₁⟩, e₁⟩,
      ⟨s₂, ⟨h₁, hpub, h₂⟩, e₂⟩⟩) fun _ _ h => h))

include hvE hctE hspE hdE hct hdC in
/-- `signC` meets `Spec.RsaPss.signContract`. -/
theorem signC_verified (H : Hash) (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) :
    Verified X86_64.target (signC encN encC privN privC) (Spec.RsaPss.signContract G G abi signStack) :=
  Verified.of_correct (k := signK G) (signC_correct hvE hspE hdE hv hC hdC)
    (signC_ct (H := H) hvE hctE hspE hdE hv hct hC hdC) (sign_implies G (sign_sat G hG))

end VG.Proof.RsaPss.X86_64
