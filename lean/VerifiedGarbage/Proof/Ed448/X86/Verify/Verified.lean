import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Impl.Ed448.X86.Verify
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Verify.Body`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Verify.Layout`. -/
section

/-!
# Ed448 verification on x86 (32-bit): the contract the proof is written against

`vfLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/VerifyMessage`):
what `vg_ed448_verify(pk, context, ctxlen, message, len, signature,
scratch)` reads (the public key, the context, the message, the signature
and its arguments) and writes (`scratch`), their separation, and the 280
bytes of stack below its return address. The inputs are public (`pub`
includes their bytes). `Facts` are its separation and bounds, and `kit` the
layout facts the calls need (`Shake.Kit`).
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

abbrev PK (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev CTX (s : State) : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
abbrev MSG (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev SIG (s : State) : Region := ⟨(arg s 5).setWidth 64, 114⟩

def vfRd (s : State) : List Region := [VG.Proof.Ed448.X86.Verify.PK s, VG.Proof.Ed448.X86.Verify.CTX s, VG.Proof.Ed448.X86.Verify.MSG s, VG.Proof.Ed448.X86.Verify.SIG s, ⟨argAddr s 0, 28⟩]
def vfWr (s : State) : List Region := [⟨(arg s 6).setWidth 64, 8192⟩]

def vfLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let sig : Region := ⟨(arg s 5).setWidth 64, 114⟩
    let scr : Region := ⟨(arg s 6).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := below (s.gpr .esp) 280
    s.rd = VG.Proof.Ed448.X86.Verify.vfRd s ∧ s.wr = VG.Proof.Ed448.X86.Verify.vfWr s ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s t := t.gpr .eax = if Spec.Ed448.verify
    (Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57)
    (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) 114) then 1 else 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧ arg s 5 = arg t 5 ∧ arg s 6 = arg t 6 ∧
    Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57 = Spec.Ed448.bytesAt t.mem ((arg t 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Ed448.bytesAt t.mem ((arg t 1).setWidth 64) (arg t 2).toNat ∧
    Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Ed448.bytesAt t.mem ((arg t 3).setWidth 64) (arg t 4).toNat ∧
    Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) 114 = Spec.Ed448.bytesAt t.mem ((arg t 5).setWidth 64) 114

structure Facts (s : State) : Prop where
  pc : (VG.Proof.Ed448.X86.Verify.PK s).Disjoint (SCR (arg s 6))
  xc : (VG.Proof.Ed448.X86.Verify.CTX s).Disjoint (SCR (arg s 6))
  mc : (VG.Proof.Ed448.X86.Verify.MSG s).Disjoint (SCR (arg s 6))
  sc : (VG.Proof.Ed448.X86.Verify.SIG s).Disjoint (SCR (arg s 6))
  ac : (VG.Proof.Ed448.X86.Shake.ARGS s 7).Disjoint (SCR (arg s 6))
  rc : (RET s).Disjoint (SCR (arg s 6))
  kp : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.Verify.PK s)
  kx : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.Verify.CTX s)
  km : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.Verify.MSG s)
  ks : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.Verify.SIG s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 6))
  pk : (arg s 0).toNat + 57 ≤ 2 ^ 32
  ctx : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  msg : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  sig : (arg s 5).toNat + 114 ≤ 2 ^ 32
  scratch : (arg s 6).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32

theorem facts {s : State} (h : vfLocal.pre s) : VG.Proof.Ed448.X86.Verify.Facts s := by
  obtain ⟨_, _, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, f, g⟩ := h
  exact ⟨pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, f, g⟩

theorem pk_in (s : State) : VG.Proof.Ed448.X86.Verify.PK s ∈ VG.Proof.Ed448.X86.Verify.vfRd s := List.mem_cons_self
theorem ctx_in (s : State) : VG.Proof.Ed448.X86.Verify.CTX s ∈ VG.Proof.Ed448.X86.Verify.vfRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem msg_in (s : State) : VG.Proof.Ed448.X86.Verify.MSG s ∈ VG.Proof.Ed448.X86.Verify.vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem sig_in (s : State) : VG.Proof.Ed448.X86.Verify.SIG s ∈ VG.Proof.Ed448.X86.Verify.vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem args_in (s : State) : VG.Proof.Ed448.X86.Shake.ARGS s 7 ∈ VG.Proof.Ed448.X86.Verify.vfRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
theorem scr_in (s : State) : SCR (arg s 6) ∈ VG.Proof.Ed448.X86.Verify.vfWr s := List.mem_cons_self

theorem kit {s : State} (h : VG.Proof.Ed448.X86.Verify.Facts s) : Kit (base s) (arg s 6) 7 (VG.Proof.Ed448.X86.Verify.vfRd s) (VG.Proof.Ed448.X86.Verify.vfWr s) := by
  refine Shake.kit h.below (by have := h.above; omega) h.scratch (VG.Proof.Ed448.X86.Verify.scr_in s) ?_ ?_ ?_ (VG.Proof.Ed448.X86.Verify.args_in s)
  · intro R hR
    rw [List.mem_singleton.mp hR]; exact h.kc
  · intro r hr R hR
    rw [List.mem_singleton.mp hR]
    simp only [VG.Proof.Ed448.X86.Verify.vfRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.pc, h.xc, h.mc, h.sc, h.ac]
  · intro r hr
    simp only [VG.Proof.Ed448.X86.Verify.vfRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kp.symm, h.kx.symm, h.km.symm, h.ks.symm,
      Shake.args_stack (n := 7) h.below (by have := h.above; omega) (by decide)]

theorem ret_out {s : State} (h : VG.Proof.Ed448.X86.Verify.Facts s) : ∀ R ∈ VG.Proof.Ed448.X86.Verify.vfWr s, (RET s).Disjoint R := by
  intro R hR
  rw [List.mem_singleton.mp hR]; exact h.rc

end VG.Proof.Ed448.X86.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Verify.Body`. -/
section

/-!
# Ed448 verification on x86 (32-bit): correctness

For any `eq` meeting `verifyEquationLocal` (`CalleeOk`): the header of
`dom4` in the frame at `HDR` (`Kit.hdr_ok`), `H(dom4(0, C) ‖ R ‖ A ‖ M)` at
`HASH` (`hash_ok`), `k`, the hash reduced modulo `L`, at `K`
(`reduce_step`, by `vg_ed448_scalar_reduce`), and `eq`'s result in `eax`
(`eq_step`); `verify_ok`: the whole function, which returns 0 at once for a
context of 256 bytes or more.
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Verify
open VG.Impl.Ed25519.X86.Whole (Value setup)
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Within Whole.FR Whole.valid Whole.call_ok Whole.CallReady)

variable {s t u : State} {g : Reg → BitVec 32} {m : Mem}

/-- The frame's invariant, from any registers and memory on entry. -/
abbrev GCtx (s : State) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.X86.Whole.Ctx (base s) g m (VG.Proof.Ed448.X86.Verify.vfRd s) (VG.Proof.Ed448.X86.Verify.vfWr s) t

theorem scr_at (s : State) : ScrAt 7 (arg s) 6 (arg s 6) := ⟨by decide, rfl⟩

theorem sig57 (s : State) : Whole.Within ⟨(arg s 5).setWidth 64, 57⟩ (VG.Proof.Ed448.X86.Verify.SIG s) :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩

/-! ## The hash -/

/-- `H(dom4(0, C) ‖ R ‖ A ‖ M)` in the frame at `HASH`, with the header of
`dom4` in the frame. -/
theorem hash_ok (h : VG.Proof.Ed448.X86.Verify.Facts s) (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg s 2)) :
    WP isa Impl.Ed448.X86.Verify.hash t fun u => VG.Proof.Ed448.X86.Verify.GCtx s g m u ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
          (Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Sha3.bytesAt m ((arg s 0).setWidth 64) 57 ++
            Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat) := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  have fa := hk.fr_addr (d := HDR) (by decide)
  unfold Impl.Ed448.X86.Verify.hash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.X86.Verify.scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := sframe_bytes hf1 (D := fr (base s) HDR 10)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hk.fr_scr (by decide)).sub_right (hk.kWr_sub _ (kWr_state _)).sub)
    (by show 10 ≤ 2 ^ 64; decide)
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (src := .frame HDR) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HDR) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide))
    (hk.fr_fit (by decide)) (VG.Proof.Ed448.X86.Shake.repr_nil hz)) fun t2 ⟨hc2, _, hr2, hp2⟩ => ?_)
  rw [fa] at hr2
  have e1 : Spec.Sha3.bytesAt t1.mem ((base s).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg s 2) :=
    hh1.trans hh
  rw [e1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 2)).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (src := .caller 1 0) (len := .caller 2 0)
    (P := arg s 1) (N := (arg s 2).toNat) (show 1 < 7 by decide) (show 2 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.ctx_in s), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.Verify.ctx_in s) (whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, _, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.Verify.CTX s) hc2 (VG.Proof.Ed448.X86.Verify.ctx_in s) (whole (VG.Proof.Ed448.X86.Verify.CTX s)) (by show (arg s 2).toNat ≤ 2 ^ 64; have := (arg s 2).isLt; omega)
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (src := .caller 5 0) (len := .const 57)
    (P := arg s 5) (N := 57) (show 5 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.sig_in s), VG.Proof.Ed448.X86.Verify.sig57 s⟩) (hk.away_input (VG.Proof.Ed448.X86.Verify.sig_in s) (VG.Proof.Ed448.X86.Verify.sig57 s))
    (by have := h.sig; omega) hr3 hp3) fun t4 ⟨hc4, _, hr4, hp4⟩ => ?_)
  have es : Spec.Sha3.bytesAt t3.mem ((arg s 5).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) 57 :=
    hk.input_bytes (D := ⟨(arg s 5).setWidth 64, 57⟩) hc3 (VG.Proof.Ed448.X86.Verify.sig_in s) (VG.Proof.Ed448.X86.Verify.sig57 s) (by show 57 ≤ 2 ^ 64; decide)
  rw [es] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (src := .caller 0 0) (len := .const 57)
    (P := arg s 0) (N := 57) (show 0 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.pk_in s), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.Verify.pk_in s) (whole _))
    h.pk hr4 hp4) fun t5 ⟨hc5, _, hr5, hp5⟩ => ?_)
  have ep : Spec.Sha3.bytesAt t4.mem ((arg s 0).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 0).setWidth 64) 57 :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.Verify.PK s) hc4 (VG.Proof.Ed448.X86.Verify.pk_in s) (whole (VG.Proof.Ed448.X86.Verify.PK s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc5 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 7 by decide) (show 4 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.msg_in s), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.Verify.msg_in s) (whole _)) h.msg
    hr5 hp5) fun t6 ⟨hc6, _, hr6, hp6⟩ => ?_)
  have em : Spec.Sha3.bytesAt t5.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.Verify.MSG s) hc5 (VG.Proof.Ed448.X86.Verify.msg_in s) (whole (VG.Proof.Ed448.X86.Verify.MSG s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (VG.Proof.Ed448.X86.Verify.scr_at s) hr6 hp6) fun t7 ⟨hc7, _, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (VG.Proof.Ed448.X86.Verify.scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, _, hb⟩ =>
    ⟨hu, ?_⟩
  rw [hb, hs7, ← VG.Proof.Ed448.X86.Shake.shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 2) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

/-! ## `k`: the hash reduced modulo `L` -/

theorem reduce_nosp : NoSp Impl.Ed448.X86.scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse Impl.Ed448.X86.scalarReduce ≤ 20 := by lit_decide

/-- The outgoing arguments of `scalar_reduce(esp + K, esp + HASH, scratch)`. -/
structure ReduceSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = base s + BitVec.ofNat 32 K
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 6

theorem reduce_setup (h : VG.Proof.Ed448.X86.Verify.Facts s) (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (.block reduceArgs) t fun u => VG.Proof.Ed448.X86.Verify.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.Verify.ReduceSlots s u := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  unfold reduceArgs
  refine WP.mono (hk.setup_ok hc ha (vs := [.frame K, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨trivial, trivial, show 6 < 7 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem reduce_pre (h : VG.Proof.Ed448.X86.Verify.Facts s) (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.ReduceSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [fr (base s) K 57, SCR (arg s 6)]) := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  have ab : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
    VG.Proof.Ed25519.X86.Whole.arg_base hu.esp
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab, fk, fh]
  exact ⟨trivial, trivial, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Offset.base_disjoint _ (by decide) (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj (lo_fr _ (by decide) (by decide)), hk.ret_disj hk.lo_scr, hk.fr_fit (by decide),
    hk.fr_fit (by decide), h.scratch, by omega⟩

theorem reduce_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [fr (base s) K 57, SCR (arg s 6)])
      (VG.Proof.Ed448.X86.Verify.vfRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.Verify.vfWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.Verify.scr_in s), whole _⟩

theorem reduce_writes (s : State) : ∀ r ∈ [fr (base s) K 57, SCR (arg s 6)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ VG.Proof.Ed448.X86.Verify.vfWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, VG.Proof.Ed448.X86.Verify.scr_in s, whole _⟩

def reduce_ready (h : VG.Proof.Ed448.X86.Verify.Facts s) (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.ReduceSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (VG.Proof.Ed448.X86.Verify.vfRd s) (VG.Proof.Ed448.X86.Verify.vfWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.Verify.reduce_pre h hu hs, VG.Proof.Ed448.X86.Verify.reduce_covers s, VG.Proof.Ed448.X86.Verify.reduce_writes s⟩

theorem reduce_call (h : VG.Proof.Ed448.X86.Verify.Facts s) (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.ReduceSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => VG.Proof.Ed448.X86.Verify.GCtx s g m v ∧
      Frame (VG.Proof.Ed448.X86.Verify.vfWr s ++ [fr (base s) K 57] ++ [Lo (base s)]) u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) VG.Proof.Ed448.X86.Verify.reduce_nosp VG.Proof.Ed448.X86.Verify.reduce_stack
    (VG.Proof.Ed448.X86.Verify.reduce_pre h hu hs) (VG.Proof.Ed448.X86.Verify.reduce_covers s) (VG.Proof.Ed448.X86.Verify.reduce_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, ?_, ?_⟩
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp [VG.Proof.Ed448.X86.Verify.vfWr], fun _ h => h⟩
    · exact ⟨Lo (base s), by simp, below_lo hk.below⟩
  · simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
      hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fk, fh] at hpost
    rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)]

/-- `k = H(…) mod L` in the frame at `K`. -/
theorem reduce_step (h : VG.Proof.Ed448.X86.Verify.Facts s) (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => VG.Proof.Ed448.X86.Verify.GCtx s g m u ∧
      Frame (VG.Proof.Ed448.X86.Verify.vfWr s ++ [fr (base s) K 57] ++ [Lo (base s)]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.Verify.reduce_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.Verify.reduce_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)]

/-! ## The equation -/

/-- The outgoing arguments of `verify_equation(pk, signature, esp + K, scratch)`. -/
structure EqSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0
  a1 : Whole.slots (base s) u 1 = arg s 5
  a2 : Whole.slots (base s) u 2 = base s + BitVec.ofNat 32 K
  a3 : Whole.slots (base s) u 3 = arg s 6

theorem eq_setup (h : VG.Proof.Ed448.X86.Verify.Facts s) (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (.block equationArgs) t fun u => VG.Proof.Ed448.X86.Verify.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.Verify.EqSlots s u := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  unfold equationArgs
  refine WP.mono (hk.setup_ok hc ha (vs := [.caller 0 0, .caller 5 0, .frame K, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 7 by decide, show 5 < 7 by decide, trivial,
      show 6 < 7 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2 a3
  exact ⟨a0, a1, a2, a3⟩

theorem eq_pre (h : VG.Proof.Ed448.X86.Verify.Facts s) (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.EqSlots s u) :
    Proof.Ed448.X86.verifyEquationLocal.pre (u.callEntry.withRegions
      [VG.Proof.Ed448.X86.Verify.PK s, VG.Proof.Ed448.X86.Verify.SIG s, fr (base s) K 57, ⟨(base s).setWidth 64, 16⟩] [SCR (arg s 6)]) := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  have ab : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
    VG.Proof.Ed25519.X86.Whole.arg_base hu.esp
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2,
    hk.slot_arg hu (j := 3) (by decide) hs.a3, ab, fk]
  exact ⟨trivial, trivial, h.pc, h.sc, hk.fr_scr (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj hk.lo_scr, h.pk, h.sig, hk.fr_fit (by decide), h.scratch, by omega⟩

theorem eq_covers (s : State) :
    Covers ([VG.Proof.Ed448.X86.Verify.PK s, VG.Proof.Ed448.X86.Verify.SIG s, fr (base s) K 57, ⟨(base s).setWidth 64, 16⟩] ++ [SCR (arg s 6)])
      (VG.Proof.Ed448.X86.Verify.vfRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.Verify.vfWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.pk_in s), whole _⟩
  · exact .inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.sig_in s), whole _⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.Verify.scr_in s), whole _⟩

theorem eq_writes (s : State) : ∀ r ∈ [SCR (arg s 6)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ VG.Proof.Ed448.X86.Verify.vfWr s, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨_, VG.Proof.Ed448.X86.Verify.scr_in s, whole _⟩

def eq_ready (h : VG.Proof.Ed448.X86.Verify.Facts s) (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.EqSlots s u) :
    Whole.CallReady Proof.Ed448.X86.verifyEquationLocal (base s) (VG.Proof.Ed448.X86.Verify.vfRd s) (VG.Proof.Ed448.X86.Verify.vfWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.Verify.eq_pre h hu hs, VG.Proof.Ed448.X86.Verify.eq_covers s, VG.Proof.Ed448.X86.Verify.eq_writes s⟩

theorem eq_call {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : VG.Proof.Ed448.X86.Verify.Facts s)
    (hu : VG.Proof.Ed448.X86.Verify.GCtx s g m u) (hs : VG.Proof.Ed448.X86.Verify.EqSlots s u) :
    WP isa (.call "vg_ed448_verify_equation" eq) u fun v => VG.Proof.Ed448.X86.Verify.GCtx s g m v ∧
      v.gpr .eax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57)
        (Spec.Ed448.bytesAt u.mem ((arg s 5).setWidth 64) 114)
        (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57) then 1 else 0 := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  refine Whole.call_ok hu hk.below hE.ok hE.nosp hE.stack (VG.Proof.Ed448.X86.Verify.eq_pre h hu hs) (VG.Proof.Ed448.X86.Verify.eq_covers s) (VG.Proof.Ed448.X86.Verify.eq_writes s)
    fun v hv _ _ ⟨s₂, _, hg, hpost⟩ => ⟨hv, ?_⟩
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_mem, arg_withRegions,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1,
    hk.slot_arg hu (j := 2) (by decide) hs.a2, fk] at hpost
  rw [← hg .eax (by decide), hpost,
    hk.entry_bytes hu (D := VG.Proof.Ed448.X86.Verify.PK s) (hk.away_input (VG.Proof.Ed448.X86.Verify.pk_in s) (whole _)).lo (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := VG.Proof.Ed448.X86.Verify.SIG s) (hk.away_input (VG.Proof.Ed448.X86.Verify.sig_in s) (whole _)).lo (by show 114 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) K 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide)]

theorem eq_step {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : VG.Proof.Ed448.X86.Verify.Facts s)
    (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) :
    WP isa (callWith equationArgs "vg_ed448_verify_equation" eq) t fun v => VG.Proof.Ed448.X86.Verify.GCtx s g m v ∧
      v.gpr .eax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57)
        (Spec.Ed448.bytesAt t.mem ((arg s 5).setWidth 64) 114)
        (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57) then 1 else 0 := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.Verify.eq_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.Verify.eq_call hE h hu hs) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  have away : ∀ D : Region, (Lo (base s)).Disjoint D → ∀ r ∈ [(⟨(base s).setWidth 64, 24⟩ : Region)], D.Disjoint r :=
    fun D hD r hr => by rw [List.mem_singleton.mp hr]; exact (hD.sub_left (args_lo _ (by decide))).symm
  rw [ho, frame_bytes hm (D := VG.Proof.Ed448.X86.Verify.PK s) (away _ (hk.away_input (VG.Proof.Ed448.X86.Verify.pk_in s) (whole _)).lo) (by show 57 ≤ 2 ^ 64; decide),
    frame_bytes hm (D := VG.Proof.Ed448.X86.Verify.SIG s) (away _ (hk.away_input (VG.Proof.Ed448.X86.Verify.sig_in s) (whole _)).lo) (by show 114 ≤ 2 ^ 64; decide),
    frame_bytes hm (D := fr (base s) K 57) (away _ (lo_fr _ (by decide) (by decide))) (by show 57 ≤ 2 ^ 64; decide)]

/-! ## The body -/

/-- What `vg_ed448_verify` returns, for a context below 256 bytes. -/
abbrev result (s : State) (m : Mem) : BitVec 32 :=
  if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57)
    (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 114)
    (Spec.Ed448.scalarReduce (Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
      (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57 ++
        Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat))) then 1 else 0

theorem body_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : VG.Proof.Ed448.X86.Verify.Facts s)
    (hc : VG.Proof.Ed448.X86.Verify.GCtx s g m t) (ha : Shake.Args (base s) 7 (arg s) m) (hcl : (arg s 2).toNat < 256) :
    WP isa (body eq) t fun u => VG.Proof.Ed448.X86.Verify.GCtx s g m u ∧ u.gpr .eax = VG.Proof.Ed448.X86.Verify.result s m := by
  have hk := VG.Proof.Ed448.X86.Verify.kit h
  refine WP.seq (WP.mono (hk.hdr_ok hc ha (j := 2) (off := HDR) (by decide) hcl (by decide))
    fun t₁ ⟨hc₁, _, hh, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.Verify.hash_ok h hc₁ ha hh) fun t₂ ⟨hc₂, hb₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.Verify.reduce_step h hc₂ ha) fun t₃ ⟨hc₃, _, hk₃⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.Verify.eq_step hE h hc₃ ha) fun u ⟨hu, ho⟩ => ⟨hu, ?_⟩
  have hb₂' : Spec.Ed448.bytesAt t₂.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) (arg s 2).toNat)
        (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) 57 ++ Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57 ++
          Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat) := hb₂
  rw [ho, hk₃, hb₂', hk.input_bytes (D := VG.Proof.Ed448.X86.Verify.PK s) hc₃ (VG.Proof.Ed448.X86.Verify.pk_in s) (whole (VG.Proof.Ed448.X86.Verify.PK s)) (by show 57 ≤ 2 ^ 64; decide),
    hk.input_bytes (D := VG.Proof.Ed448.X86.Verify.SIG s) hc₃ (VG.Proof.Ed448.X86.Verify.sig_in s) (whole (VG.Proof.Ed448.X86.Verify.SIG s)) (by show 114 ≤ 2 ^ 64; decide)]

theorem body_nosp {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) : NoSp (body eq) :=
  nosp_seq (NoSp.of_all (by decide +kernel))
    (nosp_seq
      (nosp_seq (NoSp.of_all (by decide +kernel))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
            (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
              (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
                (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
                  (nosp_seq (pad_nosp' (NoSp.of_all (by decide +kernel)))
                    (squeeze_nosp' (NoSp.of_all (by decide +kernel))))))))))
      (nosp_seq (nosp_seq (NoSp.of_all (by decide +kernel)) VG.Proof.Ed448.X86.Verify.reduce_nosp)
        (nosp_seq (NoSp.of_all (by decide +kernel)) hE.nosp)))

/-! ## The whole function -/

theorem shr8_beq (x : BitVec 32) : (x >>> 8 - 0 == 0) = decide (x.toNat < 256) := by
  have hz : x >>> 8 - (0 : BitVec 32) = x >>> 8 := BitVec.sub_zero _
  rw [hz]
  have e : (x >>> 8).toNat = x.toNat / 256 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · have : x >>> 8 = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt hx]; rfl)
    simp [this, hx]
  · have : x >>> 8 ≠ 0 := fun h' => hx (by
      have := congrArg BitVec.toNat h'
      rw [e] at this
      change x.toNat / 256 = 0 at this
      omega)
    rw [beq_eq_false_iff_ne.mpr this]
    simp [hx]

/-- The check of `ctxlen`: ZF is `ctxlen < 256`. -/
theorem check_ok {s : State} (h : VG.Proof.Ed448.X86.Verify.Facts s) (hrd : s.rd = VG.Proof.Ed448.X86.Verify.vfRd s) :
    WP isa (.block check) s fun t => t.gpr .esp = s.gpr .esp ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.zf = some (decide ((arg s 2).toNat < 256)) := by
  unfold check
  refine wp_ldm (b := .esp) (o := 12) rfl ?_ fun s1 v1 => wp_shr (n := 8) (by decide) fun s2 v2 _ =>
    wp_cmpi fun s3 v3 _ hz => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [hrd]
    exact ⟨ARGS s 7, List.mem_append_left _ (VG.Proof.Ed448.X86.Verify.args_in s),
      Shake.args_contains (n := 7) (by have := h.above; omega) (j := 2) (by decide)⟩
  · rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide)]
  · rw [v3.mem, v2.mem, v1.mem]
  · rw [v3.rd, v2.rd, v1.rd]
  · rw [v3.wr, v2.wr, v1.wr]
  · rw [v3.gpr, v2.other r hr, v1.other r hr]
  · rw [hz, v2.gpr, v1.gpr]
    exact congrArg some (VG.Proof.Ed448.X86.Verify.shr8_beq (arg s 2))

/-- The frame and the body, from the state after the check. -/
theorem framed_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) {s t : State}
    (hp : vfLocal.pre s) (he : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hg : ∀ r, r ≠ .eax → t.gpr r = s.gpr r) (hcl : (arg s 2).toNat < 256) :
    WP isa (.frame (.push (List.replicate 64 .eax)) (body eq) (.pop .edx 64)) t fun u =>
      abiPreserved s u ∧ u.gpr .eax = VG.Proof.Ed448.X86.Verify.result s s.mem := by
  have h := VG.Proof.Ed448.X86.Verify.facts hp
  have eb : base t = base s := by simp only [base, he]
  have hb : 280 ≤ (t.gpr .esp).toNat := by rw [he]; exact h.below
  have c0 := push_ctx (s := t) (hrd.trans hp.1) (hwr.trans hp.2.1) hb
  rw [eb] at c0
  have ha : Shake.Args (base s) 7 (arg s) t.mem := by rw [hm]; exact args_val s 7
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) (VG.Proof.Ed448.X86.Verify.body_nosp hE)
    (WP.mono (VG.Proof.Ed448.X86.Verify.body_ok hE h c0 ha hcl) fun u ⟨hu, ho⟩ => ⟨?_, ?_⟩)
  · have hu' : VG.Proof.Ed25519.X86.Whole.Ctx (base t) t.gpr t.mem (VG.Proof.Ed448.X86.Verify.vfRd s) (VG.Proof.Ed448.X86.Verify.vfWr s) u := by
      rw [eb]; exact hu
    refine Shake.abi_of (s' := t) (fun r hr => hg r (by rintro rfl; simp [calleeSaved] at hr)) hm
      (pop_abi (by decide) hb hu' fun R hR => ?_)
    have := VG.Proof.Ed448.X86.Verify.ret_out h R hR
    simp only [RET, he]
    exact this
  · rw [popped_gpr _ _ _ (by decide) (by decide), ho, hm]

theorem verify_ok {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) {s : State}
    (hp : vfLocal.pre s) : WP isa (VG.Impl.Ed448.X86.Verify.code eq) s fun t => abiPreserved s t ∧ vfLocal.post s t := by
  have h := VG.Proof.Ed448.X86.Verify.facts hp
  unfold VG.Impl.Ed448.X86.Verify.code
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.Verify.check_ok h hp.1) fun t ⟨he, hm, hrd, hwr, hg, hz⟩ => ?_)
  refine WP.ite _ hz (fun hcl => ?_) (fun hcl => ?_)
  · have hcl' : (arg s 2).toNat < 256 := of_decide_eq_true hcl
    refine WP.mono (VG.Proof.Ed448.X86.Verify.framed_ok hE hp he hm hrd hwr hg hcl') fun u ⟨ha, ho⟩ => ⟨ha, ?_⟩
    change u.gpr .eax = _
    have hl : (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat).length = (arg s 2).toNat := by
      simp [Spec.Ed448.bytesAt]
    rw [ho, Spec.Ed448.verify, VG.Proof.Ed448.X86.Shake.bytesAt_take57, hl]
    simp only [show (arg s 2).toNat ≤ 255 by omega, decide_true, Bool.true_and]
  · have hcl' : ¬ (arg s 2).toNat < 256 := of_decide_eq_false hcl
    refine wp_movi fun u vu => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [vu.other r (by rintro rfl; simp [calleeSaved] at hr), hg r (by rintro rfl; simp [calleeSaved] at hr)]
    · rw [vu.mem, hm]
    · change u.gpr .eax = _
      have hl : (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat).length = (arg s 2).toNat := by
        simp [Spec.Ed448.bytesAt]
      rw [vu.gpr, Spec.Ed448.verify, hl]
      simp only [show ¬ (arg s 2).toNat ≤ 255 by omega, decide_false, Bool.false_and]
      rfl

end VG.Proof.Ed448.X86.Verify

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Verify.Verified`. -/
section

/-!
# Ed448 verification on x86 (32-bit): constant time, and `Verified`

The check of `ctxlen` and the branch on it depend only on `ctxlen`, which is
public. In the frame, as for the public key: the blocks address memory only
through `esp` (or `scratch`, the same in both runs), and the calls get the
same arguments in both runs. `verify_equation`'s public data also includes
its inputs' bytes: the public key and the signature, the same in both runs
(`vfLocal.pub`), and `k`, the reduced hash of the inputs, which the proof
carries through the hash (`hash_ok`) and the reduction. `verify_verified`:
for any `eq` meeting `verifyEquationLocal` (`CalleeOk`), `code eq` meets
`Spec.Ed448.verifyContract X86.abi 280`.
-/

namespace VG.Proof.Ed448.X86.Verify

open VG VG.X86 VG.Impl.Ed448.X86.Verify
open VG.Impl.Ed448.X86.Shake (callWith hdrAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots)

variable {σ₁ σ₂ : State} {g₁ g₂ : Reg → BitVec 32}

theorem base_eq (hp : vfLocal.pub σ₁ σ₂) : base σ₂ = base σ₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : vfLocal.pub σ₁ σ₂) : vfRd σ₂ = vfRd σ₁ := by
  obtain ⟨e, a0, a1, a2, a3, a4, a5, _⟩ := hp
  simp only [vfRd, PK, CTX, MSG, SIG, argAddr, e, a0, a1, a2, a3, a4, a5]

theorem wr_eq (hp : vfLocal.pub σ₁ σ₂) : vfWr σ₂ = vfWr σ₁ := by
  simp only [vfWr, hp.2.2.2.2.2.2.2.1]

theorem args₂ (hp : vfLocal.pub σ₁ σ₂) : Shake.Args (base σ₁) 7 (arg σ₁) σ₂.mem := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, a6, _⟩ := id hp
  intro i hi
  rw [← base_eq hp, args_val σ₂ 7 i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

/-- The inputs' bytes are the same in both runs. -/
theorem inputs_eq (hp : vfLocal.pub σ₁ σ₂) :
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 0).setWidth 64) 57 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat =
      Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat =
      Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat ∧
    Spec.Ed448.bytesAt σ₂.mem ((arg σ₁ 5).setWidth 64) 114 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 114 := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, _, pk, ctx, msg, sig⟩ := hp
  rw [← a0] at pk
  rw [← a1, ← a2] at ctx
  rw [← a3, ← a4] at msg
  rw [← a5] at sig
  exact ⟨pk.symm, ctx.symm, msg.symm, sig.symm⟩

/-- The hash both runs compute. -/
abbrev HV (σ : State) (m : Mem) : List Byte :=
  Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg σ 1).setWidth 64) (arg σ 2).toNat)
    (Spec.Sha3.bytesAt m ((arg σ 5).setWidth 64) 57 ++ Spec.Sha3.bytesAt m ((arg σ 0).setWidth 64) 57 ++
      Spec.Sha3.bytesAt m ((arg σ 3).setWidth 64) (arg σ 4).toNat)

theorem hv_eq (hp : vfLocal.pub σ₁ σ₂) : HV σ₁ σ₂.mem = HV σ₁ σ₁.mem := by
  obtain ⟨pk, ctx, msg, sig⟩ := inputs_eq hp
  have r : Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 5).setWidth 64) 57 = Spec.Sha3.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 57 := by
    have := congrArg (List.take 57) sig
    rwa [bytesAt_take57, bytesAt_take57] at this
  simp only [HV]
  rw [show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 0).setWidth 64) 57 = _ from pk,
    show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 1).setWidth 64) (arg σ₁ 2).toNat = _ from ctx,
    show Spec.Sha3.bytesAt σ₂.mem ((arg σ₁ 3).setWidth 64) (arg σ₁ 4).toNat = _ from msg, r]
  rfl

abbrev Two₁ (σ₁ σ₂ : State) (g₁ g₂ : Reg → BitVec 32) :=
  Two (base σ₁) (vfRd σ₁) (vfWr σ₁) g₁ g₂ σ₁.mem σ₂.mem

/-- Bytes outside `Lo E`, as a callee sees them. -/
theorem entry_bytes' {E : BitVec 32} {t : State} (he : t.gpr .esp = E) (hE : 24 ≤ E.toNat) {D : Region}
    (h : (Lo E).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.callEntry.mem D.base D.len = Spec.Ed448.bytesAt t.mem D.base D.len :=
  frame_bytes (VG.Proof.Ed25519.X86.Whole.callEntry_frame t) (fun r hr => by
    rw [List.mem_singleton.mp hr, he]; exact (h.sub_left (below4_lo hE)).symm) hn

section
variable {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) (h : Facts σ₁)
  (hp : vfLocal.pub σ₁ σ₂) (hcl : (arg σ₁ 2).toNat < 256)

include h hp in
/-- The hash, in both runs. -/
theorem hash_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) Impl.Ed448.X86.Verify.hash
      (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  have hsc := scr_at σ₁
  have fa := hk.fr_addr (d := HDR) (by decide)
  unfold Impl.Ed448.X86.Verify.hash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HDR) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HDR) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 1 0) (len := .caller 2 0) (P := arg σ₁ 1)
    (N := (arg σ₁ 2).toNat) (show 1 < 7 by decide) (show 2 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (ctx_in σ₁), whole _⟩) (hk.away_input (ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .const 57) (P := arg σ₁ 5) (N := 57)
    (show 5 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (sig_in σ₁), sig57 σ₁⟩) (hk.away_input (sig_in σ₁) (sig57 σ₁))
    (by have := h.sig; omega) (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 0 0) (len := .const 57) (P := arg σ₁ 0) (N := 57)
    (show 0 < 7 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (pk_in σ₁), whole _⟩) (hk.away_input (pk_in σ₁) (whole _))
    h.pk (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 7 by decide) (show 4 < 7 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (msg_in σ₁), whole _⟩) (hk.away_input (msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

/-- The hash in the frame, the same in both runs. -/
abbrev HQ (σ₁ : State) (u : State) : Prop :=
  Spec.Ed448.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 HASH) 114 = HV σ₁ σ₁.mem

/-- `k` in the frame, the same in both runs. -/
abbrev KQ (σ₁ : State) (u : State) : Prop :=
  Spec.Ed448.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = Spec.Ed448.scalarReduce (HV σ₁ σ₁.mem)

include h hp hcl in
theorem front_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (.seq (.block (hdrAt 2 HDR)) Impl.Ed448.X86.Verify.hash)
      (Two₁ σ₁ σ₂ g₁ g₂ (HQ σ₁)) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  let HH : State → Prop := fun u =>
    Spec.Sha3.bytesAt u.mem ((base σ₁).setWidth 64 + BitVec.ofNat 64 HDR) 10 = hdrBytes (arg σ₁ 2)
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ HH)
    (block_ct (by taint_decide)
      (fun _ hc _ => WP.mono (hk.hdr_ok hc ha (j := 2) (off := HDR) (by decide) hcl (by decide))
        fun _ h => ⟨h.1, h.2.2.1⟩)
      (fun _ hc _ => WP.mono (hk.hdr_ok hc hb (j := 2) (off := HDR) (by decide) hcl (by decide))
        fun _ h => ⟨h.1, h.2.2.1⟩)) ?_
  refine (((hash_ct h hp).mono (P' := Two₁ σ₁ σ₂ g₁ g₂ HH)
    (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩) (fun _ _ h => h)).wp
    (F₁ := fun u => GCtx σ₁ g₁ σ₁.mem u ∧ HQ σ₁ u) (F₂ := fun u => GCtx σ₁ g₂ σ₂.mem u ∧ HQ σ₁ u)
    (fun a b hab => ⟨WP.mono (hash_ok h hab.1.1 ha hab.1.2) fun u hu => ⟨hu.1, show HQ σ₁ u from hu.2⟩,
      WP.mono (hash_ok h hab.2.1 hb hab.2.2) fun u hu => ⟨hu.1, show HQ σ₁ u from hu.2.trans (hv_eq hp)⟩⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)

include h hp in
/-- `k`, the hash reduced modulo `L`. -/
theorem reduce_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ (HQ σ₁))
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (Two₁ σ₁ σ₂ g₁ g₂ (KQ σ₁)) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  have keep : ∀ {t u : State}, Frame [⟨(base σ₁).setWidth 64, 24⟩] t.mem u.mem → HQ σ₁ t → HQ σ₁ u :=
    fun hm hq => (frame_bytes hm (D := fr (base σ₁) HASH 114) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 114 ≤ 2 ^ 64; decide)).trans hq
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ fun u => ReduceSlots σ₁ u ∧ HQ σ₁ u)
    (block_ct (by taint_decide) (fun _ hc hq => WP.mono (reduce_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq⟩)
      (fun _ hc hq => WP.mono (reduce_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq⟩)) ?_
  refine call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
    (fun _ _ _ hc hs => reduce_ready h hc hs.1)
    (fun a b ea eb ha' hb' ar aw br bw => by
      have e := hk.args_eq ea eb (k := 3) (by decide) (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        exacts [ha'.1.a0.trans hb'.1.a0.symm, ha'.1.a1.trans hb'.1.a1.symm, ha'.1.a2.trans hb'.1.a2.symm])
        ar aw br bw
      exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
    (fun _ hc hs => WP.mono (reduce_call h hc hs.1) fun _ hv => ⟨hv.1, by
      show Spec.Ed448.bytesAt _ ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = _
      rw [hv.2.2, (hs.2 : Spec.Ed448.bytesAt _ _ 114 = _)]⟩)
    (fun _ hc hs => WP.mono (reduce_call h hc hs.1) fun _ hv => ⟨hv.1, by
      show Spec.Ed448.bytesAt _ ((base σ₁).setWidth 64 + BitVec.ofNat 64 K) 57 = _
      rw [hv.2.2, (hs.2 : Spec.Ed448.bytesAt _ _ 114 = _)]⟩)

/-- What `verify_equation`'s call needs to be the same in both runs. -/
abbrev EqQ (σ₁ : State) (u : State) : Prop :=
  EqSlots σ₁ u ∧ KQ σ₁ u ∧
    Spec.Ed448.bytesAt u.mem ((arg σ₁ 0).setWidth 64) 57 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 0).setWidth 64) 57 ∧
    Spec.Ed448.bytesAt u.mem ((arg σ₁ 5).setWidth 64) 114 = Spec.Ed448.bytesAt σ₁.mem ((arg σ₁ 5).setWidth 64) 114

include hE h hp in
theorem equation_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ (KQ σ₁)) (callWith equationArgs "vg_ed448_verify_equation" eq)
      (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val σ₁ 7
  have hb := args₂ hp
  obtain ⟨pk₂, _, _, sig₂⟩ := inputs_eq hp
  have fk := hk.fr_addr (d := K) (by decide)
  have keep : ∀ {t u : State}, Frame [⟨(base σ₁).setWidth 64, 24⟩] t.mem u.mem → KQ σ₁ t → KQ σ₁ u :=
    fun hm hq => (frame_bytes hm (D := fr (base σ₁) K 57) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 57 ≤ 2 ^ 64; decide)).trans hq
  refine RelCT.seq (R := Two₁ σ₁ σ₂ g₁ g₂ (EqQ σ₁))
    (block_ct (by taint_decide)
      (fun _ hc hq => WP.mono (eq_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq,
        hk.input_bytes (D := PK σ₁) hu.1 (pk_in σ₁) (whole (PK σ₁)) (by show 57 ≤ 2 ^ 64; decide),
        hk.input_bytes (D := SIG σ₁) hu.1 (sig_in σ₁) (whole (SIG σ₁)) (by show 114 ≤ 2 ^ 64; decide)⟩)
      (fun _ hc hq => WP.mono (eq_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2, keep hu.2.1 hq,
        (hk.input_bytes (D := PK σ₁) hu.1 (pk_in σ₁) (whole (PK σ₁)) (by show 57 ≤ 2 ^ 64; decide)).trans pk₂,
        (hk.input_bytes (D := SIG σ₁) hu.1 (sig_in σ₁) (whole (SIG σ₁)) (by show 114 ≤ 2 ^ 64; decide)).trans sig₂⟩)) ?_
  refine call_ct hE.ok hE.ct (fun _ _ _ hc hs => eq_ready h hc hs.1) ?_
    (fun _ hc hs => WP.mono (eq_call hE h hc hs.1) fun _ hv => ⟨hv.1, trivial⟩)
    (fun _ hc hs => WP.mono (eq_call hE h hc hs.1) fun _ hv => ⟨hv.1, trivial⟩)
  intro a b ea eb ha' hb' ar aw br bw
  have ca : ∀ j < 4, arg a.callEntry j = Whole.slots (base σ₁) a j := fun j hj =>
    VG.Proof.Ed25519.X86.Whole.call_arg ea hk.below hk.frame (by omega)
  have cb : ∀ j < 4, arg b.callEntry j = Whole.slots (base σ₁) b j := fun j hj =>
    VG.Proof.Ed25519.X86.Whole.call_arg eb hk.below hk.frame (by omega)
  have lpk := (hk.away_input (pk_in σ₁) (whole _)).lo
  have lsig := (hk.away_input (sig_in σ₁) (whole _)).lo
  have lk := lo_fr (base σ₁) (d := K) (l := 57) (by decide) (by decide)
  simp only [Proof.Ed448.X86.verifyEquationLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_esp, arg_withRegions, ca 0 (by decide), ca 1 (by decide), ca 2 (by decide), ca 3 (by decide),
    cb 0 (by decide), cb 1 (by decide), cb 2 (by decide), cb 3 (by decide), ha'.1.a0, ha'.1.a1, ha'.1.a2,
    ha'.1.a3, hb'.1.a0, hb'.1.a1, hb'.1.a2, hb'.1.a3, fk, ea, eb]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_⟩
  · rw [entry_bytes' ea hk.below (D := PK σ₁) lpk (by show 57 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := PK σ₁) lpk (by show 57 ≤ 2 ^ 64; decide)]
    exact ha'.2.2.1.trans hb'.2.2.1.symm
  · rw [entry_bytes' ea hk.below (D := SIG σ₁) lsig (by show 114 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := SIG σ₁) lsig (by show 114 ≤ 2 ^ 64; decide)]
    exact ha'.2.2.2.trans hb'.2.2.2.symm
  · rw [entry_bytes' ea hk.below (D := fr (base σ₁) K 57) lk (by show 57 ≤ 2 ^ 64; decide),
      entry_bytes' eb hk.below (D := fr (base σ₁) K 57) lk (by show 57 ≤ 2 ^ 64; decide)]
    exact ha'.2.1.trans hb'.2.1.symm

include hE h hp hcl in
theorem body_ct :
    RelCT isa (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (body eq) (Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  unfold body
  exact RelCT.assoc ((front_ct h hp hcl).seq ((reduce_ct h hp).seq (equation_ct hE h hp)))

end

/-! ## The whole function -/

/-- After the check of `ctxlen`. -/
def After (σ t : State) : Prop :=
  t.gpr .esp = σ.gpr .esp ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr ∧
    (∀ r, r ≠ .eax → t.gpr r = σ.gpr r) ∧ t.zf = some (decide ((arg σ 2).toNat < 256))

theorem verify_ct {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) :
    ConstantTime isa vfLocal.pre vfLocal.pub (code eq) := by
  apply RelCT.constantTime
  unfold code
  refine RelCT.seq (Q := fun _ _ => True) ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.2.2.1) (by taint_decide)).wpDep (F := After)
    (fun s₁ s₂ h => ⟨check_ok (facts h.1) h.1.1, check_ok (facts h.2.1) h.2.1.1⟩)) ?_
  refine RelCT.ite ?_ ?_ ?_
  · rintro a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩
    change a.zf = b.zf
    rw [A₁.2.2.2.2.2, A₂.2.2.2.2.2, hp.2.2.2.1]
  · refine RelCT.frame (R := fun _ _ => True) ?_ ?_
    · rintro a b ⟨⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩, _⟩
      rw [A₁.1, A₂.1, hp.1]
    · rintro x y tx ty x' y' ⟨a, b, ⟨⟨_, σ₁, σ₂, ⟨p₁, p₂, hp⟩, A₁, A₂⟩, hev⟩, rfl, rfl⟩ e₁ e₂
      have hcl : (arg σ₁ 2).toNat < 256 := by
        change a.zf = some true at hev
        rw [A₁.2.2.2.2.2] at hev
        exact of_decide_eq_true (Option.some.inj hev)
      have h₁ := facts p₁
      have c₁ := push_ctx (s := a) (A₁.2.2.1.trans p₁.1) (A₁.2.2.2.1.trans p₁.2.1) (by rw [A₁.1]; exact h₁.below)
      have eb₁ : base a = base σ₁ := by simp only [base, A₁.1]
      rw [eb₁, A₁.2.1] at c₁
      have c₂ := push_ctx (s := b) (A₂.2.2.1.trans p₂.1) (A₂.2.2.2.1.trans p₂.2.1)
        (by rw [A₂.1]; exact (facts p₂).below)
      have eb₂ : base b = base σ₁ := by simp only [base, A₂.1, hp.1]
      rw [eb₂, A₂.2.1, rd_eq hp, wr_eq hp] at c₂
      exact ⟨(body_ct (g₁ := a.gpr) (g₂ := b.gpr) hE h₁ hp hcl _ _ _ _ _ _ ⟨⟨c₁, trivial⟩, ⟨c₂, trivial⟩⟩
        e₁ e₂).1, trivial⟩
  · refine RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (by taint_decide)
    rw [List.mem_singleton.mp hr]
    obtain ⟨⟨_, σ₁, σ₂, ⟨_, _, hp⟩, A₁, A₂⟩, _⟩ := h
    rw [A₁.1, A₂.1, hp.1]

/-! ## The shared contract -/

def vfWide : Contract isa := { vfLocal with
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let sig : Region := ⟨(arg s 5).setWidth 64, 114⟩
    let scr : Region := ⟨(arg s 6).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [pk, ctx, msg, sig] ∧ s.wr = [scr, args] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

theorem vfWide_pre (s : State) (h : vfWide.pre s) :
    vfLocal.pre (s.withRegions (vfRd s) (vfWr s)) := by
  obtain ⟨_, _, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, nb, g⟩ := h
  simp only [vfLocal, vfRd, vfWr, PK, CTX, MSG, SIG, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, pc, xc, mc, sc, ac, rc, kp, kx, km, ks, kc, a, b, c, d, e, nb, g⟩

def vfSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x8011 then 0x30 else
    if a = 0x8019 then 0x40 else if a = 0x801d then 0x50 else 0

def vfSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := vfSatMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩]
  wr := [⟨0x5000, 8192⟩, ⟨0x8004, 28⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem vfWide_implies : vfWide.Implies (Spec.Ed448.verifyContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vfWide, vfLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = _ at h
    rw [h, BitVec.setWidth_append_eq_right]
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, a0, a1, a2, a3, a4, a5, a6⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, sig⟩ := List.append_inj' hb (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, msg⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, a4])
    obtain ⟨pk, ctx⟩ := List.append_inj' first (by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, a2])
    exact ⟨sp, a0, a1, a2, a3, a4, a5, a6, pk, ctx, msg, sig⟩
  sat := by
    have a0 : arg vfSatState 0 = 0x1000 := by decide
    have a1 : arg vfSatState 1 = 0x2000 := by decide
    have a2 : arg vfSatState 2 = 0 := by decide
    have a3 : arg vfSatState 3 = 0x3000 := by decide
    have a4 : arg vfSatState 4 = 0 := by decide
    have a5 : arg vfSatState 5 = 0x4000 := by decide
    have a6 : arg vfSatState 6 = 0x5000 := by decide
    have e : argAddr vfSatState 0 = 0x8004 := by decide
    have esp : vfSatState.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, vfWide, vfLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using vfSatState

theorem verify_verified {eq : Prog isa} (hE : CalleeOk Proof.Ed448.X86.verifyEquationLocal eq) :
    Verified X86.target (code eq) (Spec.Ed448.verifyContract X86.abi 280) := by
  have hsat := vfWide_implies.sat_left
  have satLocal : ∃ s, vfLocal.pre s := hsat.elim fun s h => ⟨_, vfWide_pre s h⟩
  have verifiedLocal : Verified X86.target (code eq) vfLocal :=
    Verified.of_correct (fun _ h => verify_ok hE h) (verify_ct hE) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal vfRd vfWr vfWide_pre
    ?_ ?_ ?_ ?_ hsat) vfWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [vfRd, vfWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [vfWr, List.mem_singleton] at hr
    subst hr
    simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [vfWide, vfLocal, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

end VG.Proof.Ed448.X86.Verify

end
