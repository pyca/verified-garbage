import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Stages
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch

section

/-!
# ChaCha20-Poly1305 on x86 (32-bit): correctness

`seal` and `open`, from their parts.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Proof.ChaCha20.X86 (XorImpl)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

theorem APre.t_sub {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 704) : (tR s₀).Disjoint (sub s₀ k n) :=
  hp.c_t.symm.sub_right (sub_ctx s₀ h)

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the stack below the return address, the data, the
additional data and the return address. (Matching only reducibly, so that a
lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by lit_omega) (by lit_omega) (by lit_omega)
  | with_reducible exact (APre.stk_sub ‹APre _ _› (by lit_omega)).symm
  | with_reducible exact APre.stk_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact APre.d_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (APre.d_sub ‹APre _ _› (by lit_omega)).symm
  | with_reducible exact (‹APre _ _›).stk_d.symm
  | with_reducible exact APre.a_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (‹APre _ _›).stk_a.symm
  | with_reducible exact (‹APre _ _›).a_d
  | with_reducible exact APre.ret_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (‹APre _ _›).ret_d
  | with_reducible exact APre.ret_stk ‹APre _ _›
  | with_reducible exact APre.t_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (APre.t_sub ‹APre _ _› (by lit_omega)).symm
  | with_reducible exact (‹APre _ _›).stk_t.symm
  | with_reducible exact (‹APre _ _›).d_t
  | with_reducible exact (‹APre _ _›).d_t.symm
  | with_reducible exact (‹APre _ _›).ret_t
  | with_reducible exact APre.g_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (‹APre _ _›).g_stk
  | with_reducible exact (‹APre _ _›).g_d
  | with_reducible exact (‹APre _ _›).g_t
  | with_reducible assumption)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (arg s₀ 2) (arg s₀ 3).toNat :=
  ⟨hp.fit_a, hp.c_a, hp.stk_a, List.mem_append_left _ hp.a_rd⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (arg s₀ 4) (arg s₀ 5).toNat :=
  ⟨hp.fit_d, hp.c_d, hp.stk_d, List.mem_append_right _ hp.d_wr⟩

theorem hAL (s₀ : State) : AL s₀ < 2 ^ 64 := by have := (ALN s₀).isLt; simp only [AL]; omega
theorem hL (s₀ : State) : L s₀ ≤ 2 ^ 64 := by have := (LN s₀).isLt; simp only [L]; omega

/-- The return address is unchanged. -/
theorem ret_kept {s₀ : State} (hp : APre e s₀) {m₆ m' : Mem} (hi : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem m₆)
    {O : Addr} (ho : (retR s₀).Disjoint ⟨O, 16⟩)
    (hf : Frame [sub s₀ 448 128, ⟨O, 16⟩, sub s₀ 576 128, stkR s₀] m₆ m') :
    m'.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 := by
  have c : (retR s₀).Contains ((E s₀).setWidth 64) (32 / 8) := Region.contains_self _ _
  rw [hf.readW c (by rdisj_all) (by lit_omega), hi.readW c (by rdisj_all) (by lit_omega)]

theorem seal_eq (v : Impl.ChaCha20.X86.Callee) : «seal» v =
    .seq prologue (.seq (macPad (4 + 4 * 2) (8 + 4 * 2)) (.seq (.block lengths) (.seq (crypt v)
    (.seq (macPad (4 + 4 * 4) (8 + 4 * 4)) (.seq (absorbOne 32)
      (.seq (finalizeWith [.mov .ecx (.mem (Impl.ChaCha20.X86.at_ .esp 28))]) (.block restore))))))) := rfl

theorem seal_correct (v : XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa («seal» v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sealX86.post s₀ s' := by
  have hL' := hL s₀
  rw [seal_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (hAL s₀))
  refine WP.seq (WP.mono (macPad_ok hp (i := 2) (by lit_omega) (srcA hp) h₁.inv) fun s₂ ⟨i₂, f₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (lengths_ok hp i₂) fun s₃ ⟨i₃, f₃, len₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₃ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (crypt_ok v hp i₃) fun s₄ ⟨i₄, f₄, ct₄⟩ => ?_)
  have C₄ := ct₄ st₃
  rw [D₃] at C₄
  refine WP.seq (WP.mono (macPad_ok hp (i := 4) (by lit_omega) (srcD hp) i₄) fun s₅ ⟨i₅, f₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (absorbOne_ok hp i₅ (k := 32) (.inl (by omega)))
    fun s₆ ⟨i₆, f₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono (finalizeWith_ok hp i₆ (outOk_tag hp) (out_tag hp i₆)) fun s₇ ⟨h₇, f₇, tag₇⟩ => ?_)
  refine WP.mono (restore_ok hp h₇) fun s₈ ⟨cs₈, _, m₈⟩ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ (r₅ _ _ R₄))
  have L₅ : bytesAt s₅.mem (cx s₀ + BitVec.ofNat 64 32) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₅ (by rdisj_all) (by lit_omega), bytesAt_frame f₄ (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL',
      bytesAt_frame f₅ (by rdisj_all) hL', C₄]
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame hp.ret_t f₇⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (tp s₀) 16)
  rw [C₈, m₈, T₇, L₅, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_eq (v : Impl.ChaCha20.X86.Callee) : «open» v =
    .seq prologue (.seq (macPad (4 + 4 * 2) (8 + 4 * 2)) (.seq (macPad (4 + 4 * 4) (8 + 4 * 4))
    (.seq (.block lengths) (.seq (absorbOne 32) (.seq (crypt v) (.seq (finalizeWith (ptr .ecx .edi 16))
      (.seq (.block loadTag) (.block (Impl.ChaCha20Poly1305.X86.compare ++ restore))))))))) := rfl

/-- The tag computed by `open`, and `tag` still in memory and on the stack. -/
theorem finalize_open_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) :
    WP isa (finalizeWith (ptr .ecx .edi 16)) s fun s' => Fin s₀ s' ∧
      Frame [sub s₀ 448 128, sub s₀ 16 16, sub s₀ 576 128, stkR s₀] s.mem s'.mem ∧
      (∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 16) 16 = mac key msg) ∧
      s'.mem.readW (argAddr s₀ 6) 32 = TP s₀ ∧ bytesAt s'.mem (tp s₀) 16 = T0 s₀ := by
  refine WP.mono (finalizeWith_ok hp h (outOk_640 hp) out_640) fun s' ⟨h', f', t'⟩ => ?_
  rw [hp.c64 (k := 16) (by lit_omega)] at f' t'
  refine ⟨h', f', t', ?_, ?_⟩
  · rw [f'.readW (hp.arg_contains (by lit_omega)) (by rdisj_all) (by decide)]
    exact h.arg hp (by lit_omega)
  · rw [bytesAt_frame f' (by rdisj_all) (by lit_omega), bytesAt_frame h.frame (by rdisj_all) (by lit_omega)]

theorem open_correct (v : XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa («open» v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openX86.post s₀ s' := by
  have hL' := hL s₀
  rw [open_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (hAL s₀))
  refine WP.seq (WP.mono (macPad_ok hp (i := 2) (by lit_omega) (srcA hp) h₁.inv) fun s₂ ⟨i₂, f₂, r₂⟩ => ?_)
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (macPad_ok hp (i := 4) (by lit_omega) (srcD hp) i₂) fun s₃ ⟨i₃, f₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (lengths_ok hp i₃) fun s₄ ⟨i₄, f₄, len₄⟩ => ?_)
  refine WP.seq (WP.mono (absorbOne_ok hp i₄ (k := 32) (.inl (by omega)))
    fun s₅ ⟨i₅, f₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₅ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₄ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₃ (by rdisj_all),
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame f₂ (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (crypt_ok v hp i₅) fun s₆ ⟨i₆, f₆, pt₆⟩ => ?_)
  refine WP.seq (WP.mono (finalize_open_ok hp i₆) fun s₇ ⟨h₇, f₇, tag₇, tp₇, T0₇⟩ => ?_)
  refine WP.seq (WP.mono (loadTag_ok hp h₇ tp₇) fun s₇' ⟨h₇', edx₇', m₇', _⟩ => ?_)
  refine WP.block_append (WP.mono (compare_ok hp h₇' edx₇') fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ => ?_)
  have h₈ : Fin s₀ s₈ := ⟨⟨by rw [g₈ _ (by decide) (by decide), h₇'.at_.esp], by rw [rd₈, h₇'.at_.rd],
    by rw [wr₈, h₇'.at_.wr]⟩, by rw [g₈ _ (by decide) (by decide), h₇'.edi], by rw [m₈]; exact h₇'.saved⟩
  refine WP.mono (restore_ok hp h₈) fun s₉ ⟨cs₉, rax₉, m₉⟩ => ?_
  -- The tag computed, and the one received.
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame f₆ (by rdisj_all) (r₅ _ _ (Repr.frame f₄ (by rdisj_all) R₃)))
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, m₇', bytesAt_frame f₇ (by rdisj_all) hL', pt₆ st₅, bytesAt_frame f₅ (by rdisj_all) hL',
      bytesAt_frame f₄ (by rdisj_all) hL', bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  rw [len₄, D₂, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈, m₇']; exact ret_kept hp i₆.frame (hp.ret_sub (by lit_omega)) f₇⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (cx s₀ + BitVec.ofNat 64 16) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openX86, Contract.post_mk]
  rw [rax₉, rax₈, m₇', T0₇]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans hmac), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn (hm.trans he)

end VG.Proof.ChaCha20Poly1305.X86

end

section

/-!
# ChaCha20-Poly1305 on x86 (32-bit): constant time

The x86 taint analysis follows calls and frames, but not through these
functions: every callee is passed pointers into the middle of the context,
which the analysis cannot place in a region, so their stores of secrets
make it forget every public value kept in memory, the stack arguments among
them, and the callee-saved registers the callees restore from memory. So the
two runs are related piece by piece (`RelCT`): the taint analysis proves
each straight-line piece and the copy loop constant time (`taintRel`), from
the registers that the correctness proof says hold the same public values in
both runs (the pointers, the lengths and `esp`); each call of a verified
function in a frame of its arguments is constant time by the callee's own
proof (`RelCT.callWith`), its arguments being public; the branch on the
length of the tail is on a public value (`RelCT.ite`). What each run
satisfies between the pieces comes from the correctness proof
(`RelCT.post`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Proof.ChaCha20.X86 (XorImpl)
open VG.Impl.ChaCha20.X86 (at_)

variable {e : Bool}

/-! ## Tools -/

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : Taint.Hint taint.T}
    (h : (taint.check (τr rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (τr rs) (fun x y hp => agree_regs (hr x y hp)) h

/-- The final states of two runs related by `P` satisfy what correctness
says of each. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on the public data. -/
structure Pub (a b : State) : Prop where
  esp : b.gpr .esp = a.gpr .esp
  args : ∀ i < 8, arg b i = arg a i

theorem Pub.of {a b : State} (h : pubX86 a b) : Pub a b := ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

section
variable {a b : State} (hq : Pub a b)
include hq

theorem Pub.cx : arg b 7 = arg a 7 := hq.args 7 (by lit_omega)
theorem Pub.kp : arg b 0 = arg a 0 := hq.args 0 (by lit_omega)
theorem Pub.np : arg b 1 = arg a 1 := hq.args 1 (by lit_omega)
theorem Pub.dp : arg b 4 = arg a 4 := hq.args 4 (by lit_omega)
theorem Pub.ln : arg b 5 = arg a 5 := hq.args 5 (by lit_omega)
theorem Pub.tp : arg b 6 = arg a 6 := hq.args 6 (by lit_omega)

/-- The registers holding the same public values in both runs. -/
theorem Pub.inv {x y : State} (hx : Inv a x) (hy : Inv b y) :
    ∀ r ∈ [Reg.edi, .esp], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.edi, hy.edi]; exact hq.cx.symm
  · rw [hx.esp, hy.esp]; exact hq.esp.symm

theorem Pub.fin {x y : State} (hx : Fin a x) (hy : Fin b y) :
    ∀ r ∈ [Reg.edi, .esp], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.edi, hy.edi]; exact hq.cx.symm
  · rw [hx.at_.esp, hy.at_.esp]; exact hq.esp.symm

theorem Pub.c32 (k : Nat) : C32 b k = C32 a k := by simp only [C32, CX, hq.cx]

theorem Pub.at_ {x y : State} (hx : At a x) (hy : At b y) : x.gpr .esp = y.gpr .esp := by
  rw [hx.esp, hy.esp]; exact hq.esp.symm

end

/-- The callee's public data: `esp` and the arguments, which are the
registers pushed. -/
theorem entry_pub {rs : List Reg} {x y : State} (rd wr : List Region) (hrs : Reg.esp ∉ rs)
    (hfit : 4 * rs.length + 4 ≤ (x.gpr .esp).toNat) (hsp : x.gpr .esp = y.gpr .esp)
    (hr : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ((pushed rs x).callEntry.withRegions rd wr).gpr .esp = ((pushed rs y).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs x).callEntry.withRegions rd wr) i =
      arg ((pushed rs y).callEntry.withRegions rd wr) i :=
  ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp],
   fun i hi => by simp only [arg_withRegions]; exact callEntry_arg_eq hrs hfit hsp hr hi⟩

theorem regs_eq {x y : State} {rs : List Reg} (h : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ∀ r ∈ rs, x.gpr r = y.gpr r := h

/-! ## The calls -/

section
variable {a b : State} (ha : APre e a) (hb : APre e b) (hq : Pub a b)
include ha hb hq

theorem block_rel :
    RelCT isa (fun x y => Pro2 a x ∧ Pro2 b y)
      (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) fun _ _ => True :=
  RelCT.callWith Proof.ChaCha20.X86.block_correct Proof.ChaCha20.X86.block_ct (rdBlk a) (wrBlk a)
    fun x y ⟨hx, hy⟩ => by
      have py := block_pre hb hy.at_ hy.ecx hy.edx
      rw [show rdBlk b = rdBlk a by simp only [rdBlk, sub, cx, CX, E, hq.cx, hq.esp],
        show wrBlk b = wrBlk a by simp only [wrBlk, sub, cx, CX, hq.cx]] at py
      have fit := hx.at_.fit ha (rs := [.edx, .ecx]) (by decide)
      have p := entry_pub (rdBlk a) (wrBlk a) (by decide) fit (hq.at_ hx.at_ hy.at_) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.edx, hy.edx, hq.c32]
        · rw [hx.ecx, hy.ecx, hq.c32])
      exact ⟨block_pre ha hx.at_ hx.ecx hx.edx, py, hq.at_ hx.at_ hy.at_, p.1, p.2 0 (by decide),
        p.2 1 (by decide)⟩

theorem init_rel :
    RelCT isa (fun x y => Pro4 a x ∧ Pro4 b y)
      (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.init_ok Proof.Poly1305.X86.init_ct (rdInit a) (wrInit a)
    fun x y ⟨hx, hy⟩ => by
      have py := init_pre hb hy.at_ hy.ecx hy.edx
      rw [show rdInit b = rdInit a by simp only [rdInit, sub, cx, CX, E, hq.cx, hq.esp],
        show wrInit b = wrInit a by simp only [wrInit, sub, cx, CX, hq.cx]] at py
      have fit := hx.at_.fit ha (rs := [.ecx, .edx]) (by decide)
      have p := entry_pub (rdInit a) (wrInit a) (by decide) fit (hq.at_ hx.at_ hy.at_) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, hq.c32])
      exact ⟨init_pre ha hx.at_ hx.ecx hx.edx, py, hq.at_ hx.at_ hy.at_, p.1, p.2 0 (by decide),
        p.2 1 (by decide)⟩

theorem oneB_rel {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 704)) :
    RelCT isa (fun x y => OneA a k x ∧ OneA b k y)
      (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.blocks_ok Proof.Poly1305.X86.blocks_ct
    (rdBlocks a (C32 a k) 1) (wrBlocks a) fun x y ⟨hx, hy⟩ => by
      have py := blocks_pre hb hy.inv.at (n := 1) (by decide) (bsrc_ctx hb hk) hy.edx hy.ecx hy.eax
      rw [show rdBlocks b (C32 b k) 1 = rdBlocks a (C32 a k) 1 by simp only [rdBlocks, E, hq.c32, hq.esp],
        show wrBlocks b = wrBlocks a by simp only [wrBlocks, sub, cx, CX, hq.cx]] at py
      have fit := hx.inv.at.fit ha (rs := [.eax, .ecx, .edx]) (by decide)
      have p := entry_pub (rdBlocks a (C32 a k) 1) (wrBlocks a) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.eax, hy.eax]
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, hq.c32])
      exact ⟨blocks_pre ha hx.inv.at (n := 1) (by decide) (bsrc_ctx ha hk) hx.edx hx.ecx hx.eax, py,
        hq.at_ hx.inv.at hy.inv.at, p.1, p.2 0 (by decide), p.2 1 (by decide), p.2 2 (by decide)⟩

theorem maB_rel {i : Nat} (hi : i + 1 < 8) (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) :
    RelCT isa (fun x y => MA a i x ∧ MA b i y)
      (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.blocks_ok Proof.Poly1305.X86.blocks_ct
    (rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16)) (wrBlocks a) fun x y ⟨hx, hy⟩ => by
      have ei : arg b i = arg a i := hq.args i (by lit_omega)
      have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi
      have py := blocks_pre hb hy.inv.at (by decide) (hsb.bsrc (Nat.mul_div_le _ _)) hy.ecx hy.ebx hy.eax
      rw [show rdBlocks b (arg b i) ((arg b (i + 1)).toNat / 16) =
          rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16) by simp only [rdBlocks, E, ei, ei', hq.esp],
        show wrBlocks b = wrBlocks a by simp only [wrBlocks, sub, cx, CX, hq.cx]] at py
      have fit := hx.inv.at.fit ha (rs := [.eax, .ebx, .ecx]) (by decide)
      have p := entry_pub (rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16)) (wrBlocks a) (by decide) fit
        (hq.at_ hx.inv.at hy.inv.at) (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [hx.eax, hy.eax, ei']
          · rw [hx.ebx, hy.ebx, ei]
          · rw [hx.ecx, hy.ecx, hq.c32])
      exact ⟨blocks_pre ha hx.inv.at (by decide) (hsa.bsrc (Nat.mul_div_le _ _)) hx.ecx hx.ebx hx.eax, py,
        hq.at_ hx.inv.at hy.inv.at, p.1, p.2 0 (by decide), p.2 1 (by decide), p.2 2 (by decide)⟩

theorem crB_rel (v : XorImpl) :
    RelCT isa (fun x y => CrA a x ∧ CrA b y)
      (callWith [.esi, .edx, .ecx, .eax] v.callee.name v.callee.code) fun _ _ => True :=
  RelCT.callWith v.ok v.ct [] (wrXor a)
    fun x y ⟨hx, hy⟩ => by
      have py := xor_pre hb hy.inv.at hy.eax hy.ecx hy.edx hy.esi
      rw [show wrXor b = wrXor a by simp only [wrXor, sub, cx, CX, dR, dp, DP, L, LN, E, hq.cx, hq.dp, hq.ln,
        hq.esp]] at py
      have fit := hx.inv.at.fit ha (rs := [.esi, .edx, .ecx, .eax]) (by decide)
      have p := entry_pub [] (wrXor a) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hx.esi, hy.esi, hq.c32]
        · rw [hx.edx, hy.edx]; exact hq.ln.symm
        · rw [hx.ecx, hy.ecx]; exact hq.dp.symm
        · rw [hx.eax, hy.eax, hq.c32])
      exact ⟨xor_pre ha hx.inv.at hx.eax hx.ecx hx.edx hx.esi, py, hq.at_ hx.inv.at hy.inv.at, p.1,
        fun i hi => p.2 i hi⟩

theorem fiB_rel {O : State → BitVec 32} (hoa : OutOk a (O a)) (hob : OutOk b (O b)) (hO : O b = O a) :
    RelCT isa (fun x y => FiA a (O a) x ∧ FiA b (O b) y)
      (callWith finRegs "vg_poly1305_finalize_scratch" Impl.Poly1305.X86.finalize) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.finalize_ok Proof.Poly1305.X86.finalize_ct (rdFin a)
    (wrFin a (O a)) fun x y ⟨hx, hy⟩ => by
      have py := finalize_pre hb hy.inv.at hob hy.ebx hy.ecx hy.eax hy.esi
      rw [show rdFin b = rdFin a by simp only [rdFin, E, hq.esp],
        show wrFin b (O b) = wrFin a (O a) by simp only [wrFin, sub, cx, CX, hq.cx, hO]] at py
      have fit := hx.inv.at.fit ha (rs := finRegs) (by decide)
      have p := entry_pub (rdFin a) (wrFin a (O a)) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [hx.ebx, hy.ebx, hq.c32]
        · rw [hx.ecx, hy.ecx, hO]
        · rw [hx.eax, hy.eax]
        · rw [hx.eax, hy.eax]
        · rw [hx.esi, hy.esi, hq.c32])
      exact ⟨finalize_pre ha hx.inv.at hoa hx.ebx hx.ecx hx.eax hx.esi, py, hq.at_ hx.inv.at hy.inv.at, p.1,
        fun i hi => p.2 i hi⟩

/-! ## The parts -/

theorem prologue_rel :
    RelCT isa (fun x y => x = a ∧ y = b) prologue fun x y => PostP a x ∧ PostP b y := by
  rw [prologue_eq]
  refine RelCT.seq (R := fun x y => x = a.setReg .eax (CX a) ∧ y = b.setReg .eax (CX b))
    (RelCT.post (taintRel [.esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr hx hy; exact hq.esp.symm) (by taint_decide))
      fun x y ⟨hx, hy⟩ => by subst hx hy; exact ⟨load_ok ha, load_ok hb⟩) ?_
  refine RelCT.seq (R := fun x y => Pro1 a x ∧ Pro1 b y)
    (RelCT.post (taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hx hy
      rcases hr with rfl | rfl
      · simp only [State.setReg, ite_true]; exact hq.cx.symm
      · simp only [reduceCtorEq, ↓reduceIte, State.setReg]; exact hq.esp.symm) (by taint_decide))
      fun x y ⟨hx, hy⟩ => by subst hx hy; exact ⟨pro1_ok ha, pro1_ok hb⟩) ?_
  refine RelCT.seq (R := fun x y => Pro2 a x ∧ Pro2 b y)
    (RelCT.post (taintRel [.ecx, .edx, .edi, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.ecx, hy.ecx]; exact hq.kp.symm
      · rw [hx.edx, hy.edx]; exact hq.np.symm
      · rw [hx.edi, hy.edi]; exact hq.cx.symm
      · exact hq.at_ hx.at_ hy.at_) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨pro2_ok ha hx, pro2_ok hb hy⟩) ?_
  refine RelCT.seq (R := fun x y => Pro3 a x ∧ Pro3 b y)
    (RelCT.post (block_rel ha hb hq) fun x y ⟨hx, hy⟩ => ⟨pro3_ok ha hx, pro3_ok hb hy⟩) ?_
  refine RelCT.seq (R := fun x y => Pro4 a x ∧ Pro4 b y)
    (RelCT.post (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx.edi, hy.edi]; exact hq.cx.symm
      · exact hq.at_ hx.at_ hy.at_) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨pro4_ok hx, pro4_ok hy⟩) ?_
  exact RelCT.post (init_rel ha hb hq) fun x y ⟨hx, hy⟩ => ⟨post_ok ha hx, post_ok hb hy⟩

theorem absorbOne_rel {k : Nat} (hk : k = 48 ∨ k = 32) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (absorbOne k) fun _ _ => True := by
  have hk' : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 704) := by omega
  rw [absorbOne_eq]
  refine RelCT.seq (R := fun x y => OneA a k x ∧ OneA b k y)
    (RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨WP.mono (oneA_ok hx k) fun _ h => h.1,
      WP.mono (oneA_ok hy k) fun _ h => h.1⟩) (oneB_rel ha hb hq hk')
  rcases hk with rfl | rfl <;>
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)

/-- After the tail's start is computed and the block zeroed. -/
def PDz (s₀ : State) (i : Nat) (s : State) : Prop :=
  PD s₀ i s ∧ ∀ j < 16, s.mem (cx s₀ + BitVec.ofNat 64 (48 + j)) = 0

theorem padTail_rel {i : Nat} (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) (hi : i + 1 < 8) (h0 : (arg a (i + 1)).toNat % 16 ≠ 0) :
    RelCT isa (fun x y => MC a i x ∧ MC b i y) padTail fun _ _ => True := by
  have ei : arg b i = arg a i := hq.args i (by lit_omega)
  have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi
  have h0' : (arg b (i + 1)).toNat % 16 ≠ 0 := by rw [ei']; exact h0
  rw [padTail_eq]
  refine RelCT.seq (R := fun x y => PDz a i x ∧ PDz b i y)
    (RelCT.post (taintRel [.ebx, .ebp, .edx, .edi, .esp]
      (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [hx.ebx, hy.ebx, ei]
        · rw [hx.ebp, hy.ebp, ei']
        · rw [hx.edx, hy.edx, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (pd_ok ha hx) fun _ h => ⟨h.1, h.2.2⟩,
        WP.mono (pd_ok hb hy) fun _ h => ⟨h.1, h.2.2⟩⟩) ?_
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y)
    (RelCT.post (taintRel [.esi, .ecx, .edx, .edi, .esp]
      (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [hx.esi, hy.esi, ei, ei']
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ =>
        ⟨WP.mono (copy_ok ha (by rw [hx.1.inv.rd]) (by rw [hx.1.inv.wr]) hsa.tail (by lit_omega) (cp0 hx.1 hx.2))
          fun _ h => copied_inv ha hx.1 h,
         WP.mono (copy_ok hb (by rw [hy.1.inv.rd]) (by rw [hy.1.inv.wr]) hsb.tail (by lit_omega) (cp0 hy.1 hy.2))
          fun _ h => copied_inv hb hy.1 h⟩) ?_
  exact absorbOne_rel ha hb hq (.inl rfl)

theorem macPad_rel {i : Nat} (hi : i = 2 ∨ i = 4) (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (macPad (4 + 4 * i) (8 + 4 * i)) fun _ _ => True := by
  have hi' : i + 1 < 8 := by omega
  have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi'
  rw [macPad_eq]
  refine RelCT.seq (R := fun x y => MA a i x ∧ MA b i y)
    (RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨WP.mono (maA_ok ha hi' hx) fun _ h => h.1,
      WP.mono (maA_ok hb hi' hy) fun _ h => h.1⟩) ?_
  · rcases hi with rfl | rfl <;>
    exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)
  refine RelCT.seq (R := fun x y => MB a i x ∧ MB b i y)
    (RelCT.post (maB_rel ha hb hq hi' hsa hsb) fun x y ⟨hx, hy⟩ =>
      ⟨WP.mono (maB_ok ha hsa hx) fun _ h => h.1, WP.mono (maB_ok hb hsb hy) fun _ h => h.1⟩) ?_
  refine RelCT.seq (R := fun x y => MC a i x ∧ MC b i y)
    (RelCT.post (taintRel [.ebp, .edi, .esp]
      (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.ebp, hy.ebp, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (maC_ok hx) fun _ h => h.1, WP.mono (maC_ok hy) fun _ h => h.1⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.zf, hy.zf, ei'])
    (RelCT.nil fun _ _ _ => trivial) fun x y t₁ t₂ x' y' ⟨⟨hx, hy⟩, he⟩ e₁ e₂ => ?_
  have h0 : (arg a (i + 1)).toNat % 16 ≠ 0 := by
    intro h0; simp [eval, hx.zf, h0] at he
  exact padTail_rel ha hb hq hsa hsb hi' h0 x y t₁ t₂ x' y' ⟨hx, hy⟩ e₁ e₂

theorem crypt_rel (v : XorImpl) : RelCT isa (fun x y => Inv a x ∧ Inv b y) (crypt v.callee) fun _ _ => True := by
  rw [crypt_eq]
  exact RelCT.seq (R := fun x y => CrA a x ∧ CrA b y)
    (RelCT.post (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (crA_ok ha hx) fun _ h => h.1, WP.mono (crA_ok hb hy) fun _ h => h.1⟩)
    (crB_rel ha hb hq v)

theorem finalizeWith_rel {out : List Instr} {O : State → BitVec 32} (hoa : OutOk a (O a))
    (hob : OutOk b (O b)) (hO : O b = O a)
    (hta : RelCT isa (fun x y => Inv a x ∧ Inv b y)
      (.block (ptr .ebx .edi 576 ++ out ++ ([.mov .eax (.imm 0)] : List Instr) ++ ptr .esi .edi 448))
      fun _ _ => True)
    (houta : ∀ s : State, Inv a s → ∀ t : State, t.gpr .esp = E a → t.rd = a.rd → t.wr = a.wr →
      t.mem = s.mem → t.gpr .edi = CX a → WP isa (.block out) t fun t' => t'.gpr .ecx = O a ∧
        (∀ q, q ≠ .ecx → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mem = t.mem)
    (houtb : ∀ s : State, Inv b s → ∀ t : State, t.gpr .esp = E b → t.rd = b.rd → t.wr = b.wr →
      t.mem = s.mem → t.gpr .edi = CX b → WP isa (.block out) t fun t' => t'.gpr .ecx = O b ∧
        (∀ q, q ≠ .ecx → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mem = t.mem) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (finalizeWith out) fun _ _ => True := by
  rw [finalizeWith_eq]
  exact RelCT.seq (R := fun x y => FiA a (O a) x ∧ FiA b (O b) y)
    (RelCT.post hta
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (fiA_ok hx (houta x hx)) fun _ h => h.1,
        WP.mono (fiA_ok hy (houtb y hy)) fun _ h => h.1⟩) (fiB_rel ha hb hq hoa hob hO)

/-! ## The functions -/

omit hq in
/-- A part that keeps the invariant. -/
theorem inv_rel {c : Prog isa} (h : RelCT isa (fun x y => Inv a x ∧ Inv b y) c fun _ _ => True)
    (hw : ∀ s₀ s, APre e s₀ → Inv s₀ s → WP isa c s (Inv s₀)) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) c fun x y => Inv a x ∧ Inv b y :=
  RelCT.post h fun x y ⟨hx, hy⟩ => ⟨hw a x ha hx, hw b y hb hy⟩

end

theorem seal_rel {a b : State} (ha : APre true a) (hb : APre true b) (hq : Pub a b) (v : XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) («seal» v.callee) fun _ _ => True := by
  rw [seal_eq]
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y) (RelCT.mono (prologue_rel ha hb hq) (fun _ _ h => h) fun x y ⟨hx, hy⟩ => ⟨hx.inv, hy.inv⟩) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inl rfl) (srcA ha) (srcA hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by lit_omega) (srcA hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
    (fun s₀ _ hp h => WP.mono (lengths_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (crypt_rel ha hb hq v) (fun s₀ _ hp h => WP.mono (crypt_ok v hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inr rfl) (srcD ha) (srcD hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by lit_omega) (srcD hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (absorbOne_rel ha hb hq (.inr rfl))
    (fun s₀ _ hp h => WP.mono (absorbOne_ok hp h (.inl (by omega))) fun _ h => h.1)) ?_
  refine RelCT.seq (R := fun x y => Fin a x ∧ Fin b y) (RelCT.post (finalizeWith_rel ha hb hq (O := TP)
    (outOk_tag ha) (outOk_tag hb) hq.tp
    (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)) (fun _ h => out_tag ha h) (fun _ h => out_tag hb h))
    fun x y ⟨hx, hy⟩ => ⟨WP.mono (finalizeWith_ok ha hx (outOk_tag ha) (out_tag ha hx)) fun _ h => h.1,
      WP.mono (finalizeWith_ok hb hy (outOk_tag hb) (out_tag hb hy)) fun _ h => h.1⟩) ?_
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.fin hx hy) (by taint_decide)

theorem open_rel {a b : State} (ha : APre false a) (hb : APre false b) (hq : Pub a b) (v : XorImpl) :
    RelCT isa (fun x y => x = a ∧ y = b) («open» v.callee) fun _ _ => True := by
  rw [open_eq]
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y) (RelCT.mono (prologue_rel ha hb hq) (fun _ _ h => h) fun x y ⟨hx, hy⟩ => ⟨hx.inv, hy.inv⟩) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inl rfl) (srcA ha) (srcA hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by lit_omega) (srcA hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inr rfl) (srcD ha) (srcD hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by lit_omega) (srcD hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
    (fun s₀ _ hp h => WP.mono (lengths_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (absorbOne_rel ha hb hq (.inr rfl))
    (fun s₀ _ hp h => WP.mono (absorbOne_ok hp h (.inl (by omega))) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (crypt_rel ha hb hq v) (fun s₀ _ hp h => WP.mono (crypt_ok v hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (R := fun (x y : State) => (Fin a x ∧ x.mem.readW (argAddr a 6) 32 = TP a) ∧
      (Fin b y ∧ y.mem.readW (argAddr b 6) 32 = TP b))
    (RelCT.post (finalizeWith_rel ha hb hq (O := fun s => C32 s 16) (outOk_640 ha) (outOk_640 hb)
      (hq.c32 16) (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
      (fun _ _ => out_640) (fun _ _ => out_640))
    fun x y ⟨hx, hy⟩ => ⟨WP.mono (finalize_open_ok ha hx) fun _ h => ⟨h.1, h.2.2.2.1⟩,
      WP.mono (finalize_open_ok hb hy) fun _ h => ⟨h.1, h.2.2.2.1⟩⟩) ?_
  refine RelCT.seq (R := fun (x y : State) => (Fin a x ∧ x.gpr .edx = TP a) ∧ (Fin b y ∧ y.gpr .edx = TP b))
    (RelCT.post (taintRel [.esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hq.at_ hx.1.at_ hy.1.at_) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (loadTag_ok ha hx.1 hx.2) fun _ h => ⟨h.1, h.2.1⟩,
        WP.mono (loadTag_ok hb hy.1 hy.2) fun _ h => ⟨h.1, h.2.1⟩⟩) ?_
  exact taintRel [.edx, .edi, .esp] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.2, hy.2]; exact hq.tp.symm
    · rw [hx.1.edi, hy.1.edi]; exact hq.cx.symm
    · exact hq.at_ hx.1.at_ hy.1.at_) (by taint_decide)

theorem seal_ct (v : XorImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (seal_rel (APre.of _ h₁) (APre.of _ h₂) (Pub.of hp) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct (v : XorImpl) : ConstantTime isa openX86.pre openX86.pub («open» v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (open_rel (APre.of _ h₁) (APre.of _ h₂) (Pub.of hp) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.ChaCha20Poly1305.X86

end

/-!
# ChaCha20-Poly1305 on x86 (32-bit): `Verified`

Correctness and constant time (both above), and a state satisfying the
precondition, of the code with its working space as its last argument
(`sealScratchContract`, `openScratchContract`), and then of the functions,
which allocate it in a frame of 740 bytes on the stack (the return address,
the seven other arguments and the 704 bytes of working space) and wipe it
after the code (`Verified.stackScratchWiped`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Proof.ChaCha20.X86 (XorImpl)

/-- Memory whose eight argument slots (at `0x5004`) hold `0x1000` (`key`),
`0x1100` (`nonce`), `0x2000` (`aad`), `0`, `0x2100` (`data`), `0`, `0x3000`
(`tag`) and `0x6000` (`work`). -/
def satMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x5005 then 0x10 else bif Nat.beq a.toNat 0x5009 then 0x11 else bif Nat.beq a.toNat 0x500D then 0x20 else
  bif Nat.beq a.toNat 0x5015 then 0x21 else bif Nat.beq a.toNat 0x501D then 0x30 else bif Nat.beq a.toNat 0x5021 then 0x60 else 0

/-- A state satisfying `seal`'s precondition (with no additional data and no
data). -/
def sealSat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x6000, 704⟩, ⟨0x5004, 32⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩],
                 wr := [⟨0x2100, 0⟩, ⟨0x6000, 704⟩, ⟨0x5004, 32⟩] }

theorem seal_ok (v : XorImpl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.X86.«seal» v.callee) s t s' ∧ abiPreserved s s' ∧
      sealX86.post s s' :=
  seal_correct v (APre.of s hs)

theorem open_ok (v : XorImpl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.X86.«open» v.callee) s t s' ∧ abiPreserved s s' ∧
      openX86.post s s' :=
  open_correct v (APre.of s hs)

/-- The return value, `eax`, is the low half of `edx:eax`. -/
theorem low32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow]
  simp [Nat.mod_eq_of_lt this]

theorem seal_verified (v : XorImpl) :
    Verified X86.target (Impl.ChaCha20Poly1305.X86.«seal» v.callee) (sealScratchContract X86.abi 88 32) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    have a0 : arg sealSat 0 = 0x1000 := by decide
    have a1 : arg sealSat 1 = 0x1100 := by decide
    have a2 : arg sealSat 2 = 0x2000 := by decide
    have a3 : arg sealSat 3 = 0 := by decide
    have a4 : arg sealSat 4 = 0x2100 := by decide
    have a5 : arg sealSat 5 = 0 := by decide
    have a6 : arg sealSat 6 = 0x3000 := by decide
    have a7 : arg sealSat 7 = 0x6000 := by decide
    have e : argAddr sealSat 0 = 0x5004 := by decide
    have esp : sealSat.gpr .esp = 0x5000 := rfl
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealX86, Proof.ChaCha20Poly1305.preX86,
      Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using sealSat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified (v : XorImpl) :
    Verified X86.target (Impl.ChaCha20Poly1305.X86.«open» v.callee) (openScratchContract X86.abi 88 32) :=
  Verified.of_correct (open_ok v) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        simp only [Proof.ChaCha20Poly1305.openX86] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; exact low32 _ _, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => rw [h]; exact low32 _ _
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        have a0 : arg openSat 0 = 0x1000 := by decide
        have a1 : arg openSat 1 = 0x1100 := by decide
        have a2 : arg openSat 2 = 0x2000 := by decide
        have a3 : arg openSat 3 = 0 := by decide
        have a4 : arg openSat 4 = 0x2100 := by decide
        have a5 : arg openSat 5 = 0 := by decide
        have a6 : arg openSat 6 = 0x3000 := by decide
        have a7 : arg openSat 7 = 0x6000 := by decide
        have e : argAddr openSat 0 = 0x5004 := by decide
        have esp : openSat.gpr .esp = 0x5000 := rfl
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openX86, Proof.ChaCha20Poly1305.preX86,
          Proof.ChaCha20Poly1305.pubX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using openSat }

/-- `seal` and `open` never write the stack pointer. -/
theorem seal_spSafe (v : XorImpl) : (Impl.ChaCha20Poly1305.X86.«seal» v.callee).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [Impl.ChaCha20Poly1305.X86.«seal», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, Code.all, v.spSafe, Bool.and_true]
  lit_decide

theorem open_spSafe (v : XorImpl) : (Impl.ChaCha20Poly1305.X86.«open» v.callee).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [Impl.ChaCha20Poly1305.X86.«open», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, Code.all, v.spSafe, Bool.and_true]
  lit_decide

/-! ## The frame -/

/-- The frame of `withStackScratchWiped` keeps the stack pointer for any `c`
that does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratchWiped_spSafe {bytes n words : Nat} {c : Prog isa}
    (hf : (Impl.StackScratch.X86.withStackScratchWiped bytes n words (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratchWiped bytes n words c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch, Code.all,
    List.all_nil, Bool.and_eq_true] at hf ⊢
  simp_all

private theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

theorem seal_noEsp (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.«seal» v.callee).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [Impl.ChaCha20Poly1305.X86.«seal», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, Code.allInstrs, noEsp_of v.nosp, Bool.and_true]
  lit_decide

theorem open_noEsp (v : XorImpl) :
    (Impl.ChaCha20Poly1305.X86.«open» v.callee).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [Impl.ChaCha20Poly1305.X86.«open», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, Code.allInstrs, noEsp_of v.nosp, Bool.and_true]
  lit_decide

theorem seal_stackUse (v : XorImpl) : stackUse (Impl.ChaCha20Poly1305.X86.«seal» v.callee) ≤ 32 := by
  simp only [Impl.ChaCha20Poly1305.X86.«seal», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, stackUse, v.stack, Nat.max_le]
  lit_decide

theorem open_stackUse (v : XorImpl) : stackUse (Impl.ChaCha20Poly1305.X86.«open» v.callee) ≤ 32 := by
  simp only [Impl.ChaCha20Poly1305.X86.«open», Impl.ChaCha20Poly1305.X86.crypt,
    Impl.ChaCha20Poly1305.X86.callWith, stackUse, v.stack, Nat.max_le]
  lit_decide

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State := { sealSat with wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x5004, 28⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract X86.abi 772).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed (v : XorImpl) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» v.callee))
      (Spec.ChaCha20Poly1305.sealContract X86.abi 772) :=
  X86.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 88) (post := Spec.ChaCha20Poly1305.sealPost X86.abi.ptrBits) (wa := true) (stack := 32)
    (bytes := 740) (words := 176) (seal_verified v) (by decide) (seal_noEsp v) (seal_stackUse v) (by decide)
    (pre_local _ _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State := { openSat with wr := [⟨0x2100, 0⟩, ⟨0x5004, 28⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract X86.abi 772).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, openSat, sealSat, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : XorImpl) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» v.callee))
      (Spec.ChaCha20Poly1305.openContract X86.abi 772) :=
  X86.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 88) (post := Spec.ChaCha20Poly1305.openPost X86.abi.ptrBits) (wa := true) (stack := 32)
    (bytes := 740) (words := 176) (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (by decide)
    (pre_local _ _) (openPost_local _) (openPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.X86
