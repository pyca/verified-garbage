import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Impl.Ed448.X86.SignCached
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.SignCached.Layout`. -/
section

/-!
# Ed448 signing with a cached key on x86 (32-bit): the contract the proof is written against

`scLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/SignCached`): what
`vg_ed448_sign_cached(out, seed, pk, context, ctxlen, message, len, scratch)`
reads (the private and public keys, the context, the message and its
arguments) and writes (`out` and `scratch`), their separation, the 280 bytes
of stack below its return address, the public key of the private key, and a
context of at most 255 bytes. Only pointers and lengths are public. `Facts`
are its separation and bounds, and `kit` the layout facts the calls need.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 114⟩
abbrev SEED (s : State) : Region := ⟨(arg s 1).setWidth 64, 57⟩
abbrev PK (s : State) : Region := ⟨(arg s 2).setWidth 64, 57⟩
abbrev CTX (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev MSG (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩

def scRd (s : State) : List Region := [VG.Proof.Ed448.X86.SignCached.SEED s, VG.Proof.Ed448.X86.SignCached.PK s, VG.Proof.Ed448.X86.SignCached.CTX s, VG.Proof.Ed448.X86.SignCached.MSG s, ⟨argAddr s 0, 32⟩]
def scWr (s : State) : List Region := [VG.Proof.Ed448.X86.SignCached.OUT s, ⟨(arg s 7).setWidth 64, 8192⟩]

def scLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 114⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let msg : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scr : Region := ⟨(arg s 7).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := below (s.gpr .esp) 280
    s.rd = VG.Proof.Ed448.X86.SignCached.scRd s ∧ s.wr = VG.Proof.Ed448.X86.SignCached.scWr s ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
      (arg s 7).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
      Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57) ∧
      (arg s 4).toNat ≤ 255
  post s t := Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
    (Spec.Ed448.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Ed448.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2 ∧
    arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧ arg s 5 = arg t 5 ∧ arg s 6 = arg t 6 ∧ arg s 7 = arg t 7

structure Facts (s : State) : Prop where
  os : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (VG.Proof.Ed448.X86.SignCached.SEED s)
  op : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (VG.Proof.Ed448.X86.SignCached.PK s)
  ox : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (VG.Proof.Ed448.X86.SignCached.CTX s)
  om : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (VG.Proof.Ed448.X86.SignCached.MSG s)
  oa : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (VG.Proof.Ed448.X86.Shake.ARGS s 8)
  oc : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (SCR (arg s 7))
  ko : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT s)
  ro : (RET s).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT s)
  sc : (VG.Proof.Ed448.X86.SignCached.SEED s).Disjoint (SCR (arg s 7))
  pc : (VG.Proof.Ed448.X86.SignCached.PK s).Disjoint (SCR (arg s 7))
  xc : (VG.Proof.Ed448.X86.SignCached.CTX s).Disjoint (SCR (arg s 7))
  mc : (VG.Proof.Ed448.X86.SignCached.MSG s).Disjoint (SCR (arg s 7))
  ac : (VG.Proof.Ed448.X86.Shake.ARGS s 8).Disjoint (SCR (arg s 7))
  rc : (RET s).Disjoint (SCR (arg s 7))
  ks : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.SignCached.SEED s)
  kp : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.SignCached.PK s)
  kx : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.SignCached.CTX s)
  km : (below (s.gpr .esp) 280).Disjoint (VG.Proof.Ed448.X86.SignCached.MSG s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 7))
  out : (arg s 0).toNat + 114 ≤ 2 ^ 32
  seed : (arg s 1).toNat + 57 ≤ 2 ^ 32
  pk : (arg s 2).toNat + 57 ≤ 2 ^ 32
  ctx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  msg : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratch : (arg s 7).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 36 ≤ 2 ^ 32
  key : Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
  ctxlen : (arg s 4).toNat ≤ 255

theorem facts {s : State} (h : scLocal.pre s) : VG.Proof.Ed448.X86.SignCached.Facts s := by
  obtain ⟨_, _, os, op, ox, om, oa, oc, ko, ro, sc, pc, xc, mc, ac, rc, ks, kp, kx, km, kc,
    a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨os, op, ox, om, oa, oc, ko, ro, sc, pc, xc, mc, ac, rc, ks, kp, kx, km, kc, a, b, c, d, e, f, g, i, j, k⟩

theorem seed_in (s : State) : VG.Proof.Ed448.X86.SignCached.SEED s ∈ VG.Proof.Ed448.X86.SignCached.scRd s := List.mem_cons_self
theorem pk_in (s : State) : VG.Proof.Ed448.X86.SignCached.PK s ∈ VG.Proof.Ed448.X86.SignCached.scRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem ctx_in (s : State) : VG.Proof.Ed448.X86.SignCached.CTX s ∈ VG.Proof.Ed448.X86.SignCached.scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem msg_in (s : State) : VG.Proof.Ed448.X86.SignCached.MSG s ∈ VG.Proof.Ed448.X86.SignCached.scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem args_in (s : State) : VG.Proof.Ed448.X86.Shake.ARGS s 8 ∈ VG.Proof.Ed448.X86.SignCached.scRd s :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
theorem out_in (s : State) : VG.Proof.Ed448.X86.SignCached.OUT s ∈ VG.Proof.Ed448.X86.SignCached.scWr s := List.mem_cons_self
theorem scr_in (s : State) : SCR (arg s 7) ∈ VG.Proof.Ed448.X86.SignCached.scWr s := List.mem_cons_of_mem _ List.mem_cons_self

theorem kit {s : State} (h : VG.Proof.Ed448.X86.SignCached.Facts s) : Kit (base s) (arg s 7) 8 (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) := by
  refine Shake.kit h.below (by have := h.above; omega) h.scratch (VG.Proof.Ed448.X86.SignCached.scr_in s) ?_ ?_ ?_ (VG.Proof.Ed448.X86.SignCached.args_in s)
  · intro R hR
    simp only [VG.Proof.Ed448.X86.SignCached.scWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [h.ko, h.kc]
  · intro r hr R hR
    simp only [VG.Proof.Ed448.X86.SignCached.scRd, VG.Proof.Ed448.X86.SignCached.scWr, List.mem_cons, List.not_mem_nil, or_false] at hr hR
    rcases hR with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.os.symm, h.op.symm, h.ox.symm, h.om.symm, h.oa.symm, h.sc, h.pc, h.xc, h.mc, h.ac]
  · intro r hr
    simp only [VG.Proof.Ed448.X86.SignCached.scRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.ks.symm, h.kp.symm, h.kx.symm, h.km.symm,
      Shake.args_stack (n := 8) h.below (by have := h.above; omega) (by decide)]

theorem ret_out {s : State} (h : VG.Proof.Ed448.X86.SignCached.Facts s) : ∀ R ∈ VG.Proof.Ed448.X86.SignCached.scWr s, (RET s).Disjoint R := by
  intro R hR
  simp only [VG.Proof.Ed448.X86.SignCached.scWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [h.ro, h.rc]

/-- The two halves of `out`: `R`, then `r` and `S`. -/
abbrev OUT1 (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev OUT2 (s : State) : Region := ⟨(arg s 0).setWidth 64 + BitVec.ofNat 64 57, 57⟩

theorem out1_within (s : State) : VG.Proof.Ed25519.X86.Whole.Within (VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.OUT s) :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩

theorem out2_within (s : State) : VG.Proof.Ed25519.X86.Whole.Within (VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.OUT s) :=
  ⟨57, rfl, by show 57 + 57 ≤ 114; decide⟩

theorem out2_addr {s : State} (h : VG.Proof.Ed448.X86.SignCached.Facts s) : (arg s 0 + BitVec.ofNat 32 57).setWidth 64 =
    (arg s 0).setWidth 64 + BitVec.ofNat 64 57 :=
  addr_eq (by have := h.out; omega)

theorem out12 (s : State) : (VG.Proof.Ed448.X86.SignCached.OUT1 s).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT2 s) := Offset.base_disjoint _ (by decide) (by decide)

end VG.Proof.Ed448.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.SignCached.Hash`. -/
section

/-!
# Ed448 signing with a cached key on x86 (32-bit): the three hashes

`SHAKE256(seed, 114)` into the frame at `S` (`seed_ok`);
`H(dom4(0, C) ‖ prefix ‖ M)` (`nonce_ok`) and `H(dom4(0, C) ‖ R ‖ A ‖ M)`
(`chal_ok`) into the frame at `HASH`, from the header of `dom4` there, the
prefix in the frame at `K` and `R` in the first half of `out`. Each writes
only `Lo E`, the state and the sponge functions' working space, and its
output (`W`).
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed25519.X86.Whole (Value)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.Within Whole.FR)

variable {s t : State} {g : Reg → BitVec 32} {m : Mem}

/-- The frame's invariant, from any registers and memory on entry. -/
abbrev GCtx (s : State) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.X86.Whole.Ctx (base s) g m (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) t

theorem scr_at (s : State) : ScrAt 8 (arg s) 7 (arg s 7) := ⟨by decide, rfl⟩

/-- What a hash into the frame at `d` writes. -/
abbrev W (s : State) (d : Nat) : List Region := Lo (base s) :: fr (base s) d 114 :: kWr (arg s 7)

theorem lift_abs {s : State} {d : Nat} {m m' : Mem} (h : Frame (Lo (base s) :: kWr (arg s 7)) m m') :
    Frame (VG.Proof.Ed448.X86.SignCached.W s d) m m' :=
  h.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

theorem lift_zero {s : State} {d : Nat} {m m' : Mem} (h : Frame [⟨(arg s 7).setWidth 64, 200⟩] m m') :
    Frame (VG.Proof.Ed448.X86.SignCached.W s d) m m' :=
  h.mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (kWr_state _))

theorem away_lo {E scr : BitVec 32} {D : Region} (hd : Away E scr D) : ∀ r ∈ Lo E :: kWr scr, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hd.lo.symm
  · exact hd.kwr r hr

theorem away_state {E scr : BitVec 32} {D : Region} (hd : Away E scr D) :
    ∀ r ∈ [(⟨scr.setWidth 64, 200⟩ : Region)], D.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.kwr _ (kWr_state _)

section
variable (h : VG.Proof.Ed448.X86.SignCached.Facts s)
include h

/-- `SHAKE256(seed, 114)` into the frame at `S`. -/
theorem seed_ok (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : VG.Proof.Ed448.X86.Shake.Args (base s) 8 (arg s) m) :
    WP isa seedHash t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame (VG.Proof.Ed448.X86.SignCached.W s S) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57) 114 := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  unfold seedHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.X86.SignCached.scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 1 0) (len := .const 57)
    (P := arg s 1) (N := 57) (show 1 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨VG.Proof.Ed448.X86.SignCached.SEED s, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.seed_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.seed_in s) (VG.Proof.Ed448.X86.Shake.whole _))
    h.seed (VG.Proof.Ed448.X86.Shake.repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have e1 : Spec.Sha3.bytesAt t1.mem ((arg s 1).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57 :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.SEED s) hc1 (VG.Proof.Ed448.X86.SignCached.seed_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.SEED s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [e1] at hr2
  refine WP.seq (WP.mono (hk.pad_step hc2 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) hr2 (by rw [hp2, length_sbytes]))
    fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  refine WP.mono (hk.sqz_step hc3 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (d := S) (by decide) (by decide)) fun u ⟨hu, hf4, hb⟩ =>
    ⟨hu, (VG.Proof.Ed448.X86.SignCached.lift_zero hf1).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf2).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf3).trans hf4)), ?_⟩
  rw [hb, hs3, ← VG.Proof.Ed448.X86.Shake.shake256_eq]

/-- `H(dom4(0, C) ‖ P ‖ M)`, the header at `HASH` and `P` at `K`, into the frame at `HASH`. -/
theorem nonce_ok (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : VG.Proof.Ed448.X86.Shake.Args (base s) 8 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 10 = hdrBytes (arg s 4))
    {P : List Byte} (hp : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 = P) :
    WP isa nonceHash t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame (VG.Proof.Ed448.X86.SignCached.W s HASH) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
          (P ++ Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have fk := hk.fr_addr (d := K) (by decide)
  have aK : Away (base s) (arg s 7) (fr (base s) K 57) := hk.away_fr (by decide) (by decide)
  have aH : Away (base s) (arg s 7) (fr (base s) HASH 10) := hk.away_fr (by decide) (by decide)
  unfold nonceHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.X86.SignCached.scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := (sframe_bytes hf1 (D := fr (base s) HASH 10) (VG.Proof.Ed448.X86.SignCached.away_state aH) (by show 10 ≤ 2 ^ 64; decide)).trans hh
  have hp1 := (sframe_bytes hf1 (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.away_state aK) (by show 57 ≤ 2 ^ 64; decide)).trans hp
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .frame HASH) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide))) (by rw [fa]; exact aH)
    (hk.fr_fit (by decide)) (VG.Proof.Ed448.X86.Shake.repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  rw [fa, hh1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 4)).length % 136) := by rw [hp2, hdr_len]
  have hpk2 := (sframe_bytes hf2 (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.away_lo aK) (by show 57 ≤ 2 ^ 64; decide)).trans hp1
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.ctx_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.ctx_in s) (VG.Proof.Ed448.X86.Shake.whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.CTX s) hc2 (VG.Proof.Ed448.X86.SignCached.ctx_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.CTX s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [ex] at hr3 hp3
  have hpk3 := (sframe_bytes hf3 (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.away_lo aK) (by show 57 ≤ 2 ^ 64; decide)).trans hpk2
  -- The prefix.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .frame K) (len := .const 57)
    (P := base s + BitVec.ofNat 32 K) (N := 57) trivial trivial rfl rfl
    (by rw [fk]; exact .inl (frame_within _ (by decide))) (by rw [fk]; exact aK)
    (hk.fr_fit (by decide)) hr3 hp3) fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  rw [fk, hpk3] at hr4 hp4
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 5 0) (len := .caller 6 0)
    (P := arg s 5) (N := (arg s 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.msg_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.msg_in s) (VG.Proof.Ed448.X86.Shake.whole _)) h.msg
    hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have em : Spec.Sha3.bytesAt t4.mem ((arg s 5).setWidth 64) (arg s 6).toNat =
      Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.MSG s) hc4 (VG.Proof.Ed448.X86.SignCached.msg_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.MSG s)) (by show (arg s 6).toNat ≤ 2 ^ 64; have := (arg s 6).isLt; omega)
  rw [em] at hr5 hp5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc5 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) hr5 hp5) fun t6 ⟨hc6, hf6, hs6⟩ => ?_)
  refine WP.mono (hk.sqz_step hc6 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf7, hb⟩ =>
    ⟨hu, (VG.Proof.Ed448.X86.SignCached.lift_zero hf1).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf2).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf3).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf4).trans
      ((VG.Proof.Ed448.X86.SignCached.lift_abs hf5).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf6).trans hf7))))), ?_⟩
  rw [hb, hs6, ← VG.Proof.Ed448.X86.Shake.shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 4) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

/-- `H(dom4(0, C) ‖ R ‖ A ‖ M)`, the header at `HASH` and `R` in the first
half of `out`, into the frame at `HASH`. -/
theorem chal_ok (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : VG.Proof.Ed448.X86.Shake.Args (base s) 8 (arg s) m)
    (hh : Spec.Sha3.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 10 = hdrBytes (arg s 4))
    {R : List Byte} (hR : Spec.Sha3.bytesAt t.mem ((arg s 0).setWidth 64) 57 = R) :
    WP isa chalHash t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame (VG.Proof.Ed448.X86.SignCached.W s HASH) t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
          (R ++ Spec.Sha3.bytesAt m ((arg s 2).setWidth 64) 57 ++
            Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have aR : Away (base s) (arg s 7) (VG.Proof.Ed448.X86.SignCached.OUT1 s) := hk.away_output (VG.Proof.Ed448.X86.SignCached.out_in s) h.oc (VG.Proof.Ed448.X86.SignCached.out1_within s)
  have aH : Away (base s) (arg s 7) (fr (base s) HASH 10) := hk.away_fr (by decide) (by decide)
  unfold chalHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.X86.SignCached.scr_at s)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := (sframe_bytes hf1 (D := fr (base s) HASH 10) (VG.Proof.Ed448.X86.SignCached.away_state aH) (by show 10 ≤ 2 ^ 64; decide)).trans hh
  have hR1 := (sframe_bytes hf1 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.away_state aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR
  -- The header.
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .frame HASH) (len := .const 10)
    (P := base s + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide))) (by rw [fa]; exact aH)
    (hk.fr_fit (by decide)) (VG.Proof.Ed448.X86.Shake.repr_nil hz)) fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  rw [fa, hh1] at hr2
  have hp2' : t2.gpr .eax = BitVec.ofNat 32 ((hdrBytes (arg s 4)).length % 136) := by rw [hp2, hdr_len]
  have hR2 := (sframe_bytes hf2 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.away_lo aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR1
  -- The context.
  refine WP.seq (WP.mono (hk.next_abs hc2 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 3 0) (len := .caller 4 0)
    (P := arg s 3) (N := (arg s 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.ctx_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.ctx_in s) (VG.Proof.Ed448.X86.Shake.whole _)) h.ctx
    hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex : Spec.Sha3.bytesAt t2.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Sha3.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.CTX s) hc2 (VG.Proof.Ed448.X86.SignCached.ctx_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.CTX s)) (by show (arg s 4).toNat ≤ 2 ^ 64; have := (arg s 4).isLt; omega)
  rw [ex] at hr3 hp3
  have hR3 := (sframe_bytes hf3 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.away_lo aR) (by show 57 ≤ 2 ^ 64; decide)).trans hR2
  -- `R`.
  refine WP.seq (WP.mono (hk.next_abs hc3 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 0 0) (len := .const 57)
    (P := arg s 0) (N := 57) (show 0 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out1_within s⟩) aR (by have := h.out; omega) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  rw [hR3] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.next_abs hc4 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 2 0) (len := .const 57)
    (P := arg s 2) (N := 57) (show 2 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.pk_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.pk_in s) (VG.Proof.Ed448.X86.Shake.whole _)) h.pk
    hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have ep : Spec.Sha3.bytesAt t4.mem ((arg s 2).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 2).setWidth 64) 57 :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.PK s) hc4 (VG.Proof.Ed448.X86.SignCached.pk_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.PK s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.next_abs hc5 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (src := .caller 5 0) (len := .caller 6 0)
    (P := arg s 5) (N := (arg s 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.msg_in s), VG.Proof.Ed448.X86.Shake.whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.msg_in s) (VG.Proof.Ed448.X86.Shake.whole _)) h.msg
    hr5 hp5) fun t6 ⟨hc6, hf6, hr6, hp6⟩ => ?_)
  have em : Spec.Sha3.bytesAt t5.mem ((arg s 5).setWidth 64) (arg s 6).toNat =
      Spec.Sha3.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat :=
    hk.input_bytes (D := VG.Proof.Ed448.X86.SignCached.MSG s) hc5 (VG.Proof.Ed448.X86.SignCached.msg_in s) (VG.Proof.Ed448.X86.Shake.whole (VG.Proof.Ed448.X86.SignCached.MSG s)) (by show (arg s 6).toNat ≤ 2 ^ 64; have := (arg s 6).isLt; omega)
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) hr6 hp6) fun t7 ⟨hc7, hf7, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (VG.Proof.Ed448.X86.SignCached.scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf8, hb⟩ =>
    ⟨hu, (VG.Proof.Ed448.X86.SignCached.lift_zero hf1).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf2).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf3).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf4).trans
      ((VG.Proof.Ed448.X86.SignCached.lift_abs hf5).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf6).trans ((VG.Proof.Ed448.X86.SignCached.lift_abs hf7).trans hf8)))))), ?_⟩
  rw [hb, hs7, ← VG.Proof.Ed448.X86.Shake.shake256_eq, Spec.Ed448.hash, dom4_eq (arg s 4) _ _ (length_sbytes _ _ _)]
  simp only [List.append_assoc]

end

end VG.Proof.Ed448.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.SignCached.Calls`. -/
section

/-!
# Ed448 signing with a cached key on x86 (32-bit): the scalar calls

Each call's arguments set up in the outgoing slots (`…Slots`, `…_setup`),
its contract's precondition from them (`…_pre`, `…_ready`), and what it
leaves (`…_call`), for `r` (`vg_ed448_scalar_reduce` into the second half of
`out`), `R` (`base`, into the first half), `k` (`vg_ed448_scalar_reduce`
into the frame at `K`) and `S` (`vg_ed448_scalar_mul_add` over `r`).
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed25519.X86.Whole (Value)
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Within Whole.FR Whole.call_ok Whole.CallReady)

variable {s t u : State} {g : Reg → BitVec 32} {m : Mem}

theorem reduce_nosp : NoSp Impl.Ed448.X86.scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse Impl.Ed448.X86.scalarReduce ≤ 20 := by lit_decide
theorem mulAdd_nosp : NoSp Impl.Ed448.X86.scalarMulAdd := NoSp.of_all (by lit_decide)
theorem mulAdd_stack : stackUse Impl.Ed448.X86.scalarMulAdd ≤ 20 := by lit_decide


section
variable (h : VG.Proof.Ed448.X86.SignCached.Facts s)
include h

theorem out_lo : (Lo (base s)).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT s) := ((VG.Proof.Ed448.X86.SignCached.kit h).ko _ (VG.Proof.Ed448.X86.SignCached.out_in s)).sub_left (lo_sub _)
theorem out1_lo : (Lo (base s)).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT1 s) := (VG.Proof.Ed448.X86.SignCached.out_lo h).sub_right (VG.Proof.Ed448.X86.SignCached.out1_within s).sub
theorem out2_lo : (Lo (base s)).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT2 s) := (VG.Proof.Ed448.X86.SignCached.out_lo h).sub_right (VG.Proof.Ed448.X86.SignCached.out2_within s).sub
theorem out1_scr : (VG.Proof.Ed448.X86.SignCached.OUT1 s).Disjoint (SCR (arg s 7)) := h.oc.sub_left (VG.Proof.Ed448.X86.SignCached.out1_within s).sub
theorem out2_scr : (VG.Proof.Ed448.X86.SignCached.OUT2 s).Disjoint (SCR (arg s 7)) := h.oc.sub_left (VG.Proof.Ed448.X86.SignCached.out2_within s).sub

theorem out2_fit : (arg s 0 + BitVec.ofNat 32 57).toNat + 57 ≤ 2 ^ 32 := by
  have := h.out
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 57) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

omit h in
theorem ab_eq (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
  VG.Proof.Ed25519.X86.Whole.arg_base hu.esp

/-! ## `r` -/

structure RSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0 + BitVec.ofNat 32 57
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem r_setup (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block reduceRArgs) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.SignCached.RSlots s u := by
  unfold reduceRArgs
  refine WP.mono ((VG.Proof.Ed448.X86.SignCached.kit h).setup_ok hc ha (vs := [.caller 0 57, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, trivial, show 7 < 8 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem r_pre (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.RSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7)]) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, VG.Proof.Ed448.X86.SignCached.ab_eq hu, fh,
    VG.Proof.Ed448.X86.SignCached.out2_addr h]
  exact ⟨trivial, trivial, VG.Proof.Ed448.X86.SignCached.out2_scr h, hk.fr_scr (by decide), Kit.args_disj (by decide) (VG.Proof.Ed448.X86.SignCached.out2_lo h),
    Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (VG.Proof.Ed448.X86.SignCached.out2_lo h), hk.ret_disj hk.lo_scr, VG.Proof.Ed448.X86.SignCached.out2_fit h,
    hk.fr_fit (by decide), h.scratch, by omega⟩

omit h in
theorem r_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7)])
      (VG.Proof.Ed448.X86.SignCached.scRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.SignCached.scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out2_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.scr_in s), whole _⟩

omit h in
theorem r_writes (s : State) : ∀ r ∈ [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ VG.Proof.Ed448.X86.SignCached.scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, VG.Proof.Ed448.X86.SignCached.out_in s, VG.Proof.Ed448.X86.SignCached.out2_within s⟩
  · exact .inr ⟨_, VG.Proof.Ed448.X86.SignCached.scr_in s, whole _⟩

def r_ready (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.RSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.SignCached.r_pre h hu hs, VG.Proof.Ed448.X86.SignCached.r_covers s, VG.Proof.Ed448.X86.SignCached.r_writes s⟩

/-- A call's frame, into a list of the regions it may write and `Lo E`. -/
theorem call_frame3 {a b : Region} {m₁ m₂ : Mem} (hf : Frame ([a, b] ++ [VG.X86.below (base s) 24]) m₁ m₂) :
    Frame [a, b, Lo (base s)] m₁ m₂ := by
  refine Frame.sub hf fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨r, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨r, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨Lo (base s), by simp, below_lo (VG.Proof.Ed448.X86.SignCached.kit h).below⟩

theorem r_call (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.RSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => VG.Proof.Ed448.X86.SignCached.GCtx s g m v ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) VG.Proof.Ed448.X86.SignCached.reduce_nosp VG.Proof.Ed448.X86.SignCached.reduce_stack
    (VG.Proof.Ed448.X86.SignCached.r_pre h hu hs) (VG.Proof.Ed448.X86.SignCached.r_covers s) (VG.Proof.Ed448.X86.SignCached.r_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, VG.Proof.Ed448.X86.SignCached.call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fh, VG.Proof.Ed448.X86.SignCached.out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
    (by show 114 ≤ 2 ^ 64; decide)]

/-! ## `R` -/

structure BSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0
  a1 : Whole.slots (base s) u 1 = arg s 0 + BitVec.ofNat 32 57
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem b_setup (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block baseArgs) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.SignCached.BSlots s u := by
  unfold baseArgs
  refine WP.mono ((VG.Proof.Ed448.X86.SignCached.kit h).setup_ok hc ha (vs := [.caller 0 0, .caller 0 57, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, show 0 < 8 by decide,
      show 7 < 8 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem b_pre (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.BSlots s u) :
    scalarBaseLocal.pre (u.callEntry.withRegions [VG.Proof.Ed448.X86.SignCached.OUT2 s, ⟨(base s).setWidth 64, 12⟩] [VG.Proof.Ed448.X86.SignCached.OUT1 s, SCR (arg s 7)]) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, VG.Proof.Ed448.X86.SignCached.ab_eq hu,
    VG.Proof.Ed448.X86.SignCached.out2_addr h]
  exact ⟨trivial, trivial, VG.Proof.Ed448.X86.SignCached.out1_scr h, VG.Proof.Ed448.X86.SignCached.out2_scr h, Kit.args_disj (by decide) (VG.Proof.Ed448.X86.SignCached.out1_lo h),
    Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (VG.Proof.Ed448.X86.SignCached.out1_lo h), hk.ret_disj hk.lo_scr,
    by have := h.out; omega, VG.Proof.Ed448.X86.SignCached.out2_fit h, h.scratch, by omega⟩

omit h in
theorem b_covers (s : State) :
    Covers ([VG.Proof.Ed448.X86.SignCached.OUT2 s, ⟨(base s).setWidth 64, 12⟩] ++ [VG.Proof.Ed448.X86.SignCached.OUT1 s, SCR (arg s 7)]) (VG.Proof.Ed448.X86.SignCached.scRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.SignCached.scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out2_within s⟩
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out1_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.scr_in s), whole _⟩

omit h in
theorem b_writes (s : State) : ∀ r ∈ [VG.Proof.Ed448.X86.SignCached.OUT1 s, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ VG.Proof.Ed448.X86.SignCached.scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, VG.Proof.Ed448.X86.SignCached.out_in s, VG.Proof.Ed448.X86.SignCached.out1_within s⟩
  · exact .inr ⟨_, VG.Proof.Ed448.X86.SignCached.scr_in s, whole _⟩

def b_ready (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.BSlots s u) :
    Whole.CallReady scalarBaseLocal (base s) (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.SignCached.b_pre h hu hs, VG.Proof.Ed448.X86.SignCached.b_covers s, VG.Proof.Ed448.X86.SignCached.b_writes s⟩

theorem b_call {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.BSlots s u) :
    WP isa (.call "vg_ed448_scalar_base" base') u fun v => VG.Proof.Ed448.X86.SignCached.GCtx s g m v ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT1 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  refine Whole.call_ok hu hk.below hB.ok hB.nosp hB.stack (VG.Proof.Ed448.X86.SignCached.b_pre h hu hs) (VG.Proof.Ed448.X86.SignCached.b_covers s) (VG.Proof.Ed448.X86.SignCached.b_writes s)
    fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, VG.Proof.Ed448.X86.SignCached.call_frame3 h hf, ?_⟩
  simp only [scalarBaseLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, VG.Proof.Ed448.X86.SignCached.out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.out2_lo h) (by show 57 ≤ 2 ^ 64; decide)]

/-! ## `k` -/

structure KSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = base s + BitVec.ofNat 32 K
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 7

theorem k_setup (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block reduceKArgs) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.SignCached.KSlots s u := by
  unfold reduceKArgs
  refine WP.mono ((VG.Proof.Ed448.X86.SignCached.kit h).setup_ok hc ha (vs := [.frame K, .frame HASH, .caller SC 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨trivial, trivial, show 7 < 8 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem k_pre (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.KSlots s u) :
    Proof.Ed448.X86.scalarReduceLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] [fr (base s) K 57, SCR (arg s 7)]) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, VG.Proof.Ed448.X86.SignCached.ab_eq hu, fk, fh]
  exact ⟨trivial, trivial, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Offset.base_disjoint _ (by decide) (by decide), Kit.args_disj (by decide) hk.lo_scr,
    hk.ret_disj (lo_fr _ (by decide) (by decide)), hk.ret_disj hk.lo_scr, hk.fr_fit (by decide),
    hk.fr_fit (by decide), h.scratch, by omega⟩

omit h in
theorem k_covers (s : State) :
    Covers ([fr (base s) HASH 114, ⟨(base s).setWidth 64, 12⟩] ++ [fr (base s) K 57, SCR (arg s 7)])
      (VG.Proof.Ed448.X86.SignCached.scRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.SignCached.scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.scr_in s), whole _⟩

omit h in
theorem k_writes (s : State) : ∀ r ∈ [fr (base s) K 57, SCR (arg s 7)],
    Whole.Within r (Whole.FR (base s)) ∨ ∃ R ∈ VG.Proof.Ed448.X86.SignCached.scWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inr ⟨_, VG.Proof.Ed448.X86.SignCached.scr_in s, whole _⟩

def k_ready (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.KSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarReduceLocal (base s) (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.SignCached.k_pre h hu hs, VG.Proof.Ed448.X86.SignCached.k_covers s, VG.Proof.Ed448.X86.SignCached.k_writes s⟩

theorem k_call (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.KSlots s u) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) u fun v => VG.Proof.Ed448.X86.SignCached.GCtx s g m v ∧
      Frame [fr (base s) K 57, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fh := hk.fr_addr (d := HASH) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) VG.Proof.Ed448.X86.SignCached.reduce_nosp VG.Proof.Ed448.X86.SignCached.reduce_stack
    (VG.Proof.Ed448.X86.SignCached.k_pre h hu hs) (VG.Proof.Ed448.X86.SignCached.k_covers s) (VG.Proof.Ed448.X86.SignCached.k_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, VG.Proof.Ed448.X86.SignCached.call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarReduceLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1, fk, fh] at hpost
  rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 114) (lo_fr _ (by decide) (by decide))
    (by show 114 ≤ 2 ^ 64; decide)]

/-! ## `S` -/

structure MSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0 + BitVec.ofNat 32 57
  a1 : Whole.slots (base s) u 1 = arg s 0 + BitVec.ofNat 32 57
  a2 : Whole.slots (base s) u 2 = base s + BitVec.ofNat 32 K
  a3 : Whole.slots (base s) u 3 = base s + BitVec.ofNat 32 S
  a4 : Whole.slots (base s) u 4 = arg s 7

theorem m_setup (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (.block mulAddArgs) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      VG.Proof.Ed448.X86.SignCached.MSlots s u := by
  unfold mulAddArgs
  refine WP.mono ((VG.Proof.Ed448.X86.SignCached.kit h).setup_ok hc ha (vs := [.caller 0 57, .caller 0 57, .frame K, .frame S, .caller SC 0])
    (by decide) (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 8 by decide, show 0 < 8 by decide,
      trivial, trivial, show 7 < 8 by decide, fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2 a3 a4
  exact ⟨a0, a1, a2, a3, a4⟩

theorem m_pre (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.MSlots s u) :
    Proof.Ed448.X86.scalarMulAddLocal.pre (u.callEntry.withRegions
      [VG.Proof.Ed448.X86.SignCached.OUT2 s, fr (base s) K 57, fr (base s) S 57, ⟨(base s).setWidth 64, 20⟩] [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7)]) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fs := hk.fr_addr (d := S) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  simp only [Proof.Ed448.X86.scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2,
    hk.slot_arg hu (j := 3) (by decide) hs.a3, hk.slot_arg hu (j := 4) (by decide) hs.a4, VG.Proof.Ed448.X86.SignCached.ab_eq hu, fk, fs,
    VG.Proof.Ed448.X86.SignCached.out2_addr h]
  exact ⟨trivial, trivial, VG.Proof.Ed448.X86.SignCached.out2_scr h, VG.Proof.Ed448.X86.SignCached.out2_scr h, hk.fr_scr (by decide), hk.fr_scr (by decide),
    Kit.args_disj (by decide) (VG.Proof.Ed448.X86.SignCached.out2_lo h), Kit.args_disj (by decide) hk.lo_scr, hk.ret_disj (VG.Proof.Ed448.X86.SignCached.out2_lo h),
    hk.ret_disj hk.lo_scr, VG.Proof.Ed448.X86.SignCached.out2_fit h, VG.Proof.Ed448.X86.SignCached.out2_fit h, hk.fr_fit (by decide), hk.fr_fit (by decide), h.scratch,
    by omega⟩

omit h in
theorem m_covers (s : State) :
    Covers ([VG.Proof.Ed448.X86.SignCached.OUT2 s, fr (base s) K 57, fr (base s) S 57, ⟨(base s).setWidth 64, 20⟩] ++ [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7)])
      (VG.Proof.Ed448.X86.SignCached.scRd s ++ Whole.FR (base s) :: VG.Proof.Ed448.X86.SignCached.scWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out2_within s⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in s), VG.Proof.Ed448.X86.SignCached.out2_within s⟩
  · exact .inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.scr_in s), whole _⟩

def m_ready (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.MSlots s u) :
    Whole.CallReady Proof.Ed448.X86.scalarMulAddLocal (base s) (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s) u :=
  ⟨_, _, VG.Proof.Ed448.X86.SignCached.m_pre h hu hs, VG.Proof.Ed448.X86.SignCached.m_covers s, VG.Proof.Ed448.X86.SignCached.r_writes s⟩

theorem m_call (hu : VG.Proof.Ed448.X86.SignCached.GCtx s g m u) (hs : VG.Proof.Ed448.X86.SignCached.MSlots s u) :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) u fun v => VG.Proof.Ed448.X86.SignCached.GCtx s g m v ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7), Lo (base s)] u.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 57) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have fk := hk.fr_addr (d := K) (by decide)
  have fs := hk.fr_addr (d := S) (by decide)
  refine Whole.call_ok hu hk.below (fun s h => Proof.Ed448.X86.scalarMulAdd_ok s h) VG.Proof.Ed448.X86.SignCached.mulAdd_nosp VG.Proof.Ed448.X86.SignCached.mulAdd_stack
    (VG.Proof.Ed448.X86.SignCached.m_pre h hu hs) (VG.Proof.Ed448.X86.SignCached.m_covers s) (VG.Proof.Ed448.X86.SignCached.r_writes s) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, VG.Proof.Ed448.X86.SignCached.call_frame3 h hf, ?_⟩
  simp only [Proof.Ed448.X86.scalarMulAddLocal, State.withRegions_mem, arg_withRegions, hm₂,
    hk.slot_arg hu (j := 0) (by decide) hs.a0, hk.slot_arg hu (j := 1) (by decide) hs.a1,
    hk.slot_arg hu (j := 2) (by decide) hs.a2, hk.slot_arg hu (j := 3) (by decide) hs.a3, fk, fs,
    VG.Proof.Ed448.X86.SignCached.out2_addr h] at hpost
  rw [hpost, hk.entry_bytes hu (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.out2_lo h) (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) K 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide),
    hk.entry_bytes hu (D := fr (base s) S 57) (lo_fr _ (by decide) (by decide)) (by show 57 ≤ 2 ^ 64; decide)]

end

end VG.Proof.Ed448.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.SignCached.Body`. -/
section

/-!
# Ed448 signing with a cached key on x86 (32-bit): correctness

The steps of `body` in order (`Impl/Ed448/X86/SignCached.lean`), each with
what it leaves and what it writes; the values the later steps use are
carried past the steps in between (each outside what they write), and the
signature is `Spec.Ed448.sign`'s by `Proof.Ed448.sign_pipeline`.
`signCached_ok`: the whole function, in Ed25519's frame on this target.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed448.X86.Shake (callWith hdrAt pruneAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.Within Whole.FR Whole.Ctx.zeroWords)

variable {s t : State} {g : Reg → BitVec 32} {m : Mem}

theorem drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  have e := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, show (114 : Nat) = 57 + 57 from rfl, e,
    List.drop_left' l]

theorem split114 (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 114 = Spec.Ed448.bytesAt m p 57 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq,
    show (114 : Nat) = 57 + 57 from rfl, Proof.X25519.bytesAt_add]

section
variable (h : VG.Proof.Ed448.X86.SignCached.Facts s)
include h

/-! ## What each step writes, and what it does not -/

theorem dW {D : Region} {d : Nat} (hlo : (Lo (base s)).Disjoint D) (hfr : D.Disjoint (fr (base s) d 114))
    (hscr : D.Disjoint (SCR (arg s 7))) : ∀ r ∈ VG.Proof.Ed448.X86.SignCached.W s d, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hlo.symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hfr
  · exact hscr.sub_right ((VG.Proof.Ed448.X86.SignCached.kit h).kWr_sub r hr).sub

omit h in
theorem d3 {D a b c : Region} (ha : D.Disjoint a) (hb : D.Disjoint b) (hc : D.Disjoint c) :
    ∀ r ∈ [a, b, c], D.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [ha, hb, hc]

omit h in
theorem d1 {D a : Region} (ha : D.Disjoint a) : ∀ r ∈ [a], D.Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]; exact ha

theorem fr_out {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT s) :=
  ((VG.Proof.Ed448.X86.SignCached.kit h).ko _ (VG.Proof.Ed448.X86.SignCached.out_in s)).sub_left (frame_sub_stk _ hd)

theorem fr_out1 {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT1 s) :=
  (VG.Proof.Ed448.X86.SignCached.fr_out h hd).sub_right (VG.Proof.Ed448.X86.SignCached.out1_within s).sub

theorem fr_out2 {d : Nat} (hd : d + 57 ≤ 256) : (fr (base s) d 57).Disjoint (VG.Proof.Ed448.X86.SignCached.OUT2 s) :=
  (VG.Proof.Ed448.X86.SignCached.fr_out h hd).sub_right (VG.Proof.Ed448.X86.SignCached.out2_within s).sub

theorem out_fr {d l : Nat} (hd : d + l ≤ 256) : (VG.Proof.Ed448.X86.SignCached.OUT s).Disjoint (fr (base s) d l) :=
  (((VG.Proof.Ed448.X86.SignCached.kit h).ko _ (VG.Proof.Ed448.X86.SignCached.out_in s)).sub_left (frame_sub_stk _ hd)).symm

/-! ## The scalar steps -/

theorem r_step (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.r_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.SignCached.r_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 114 ≤ 2 ^ 64; decide)]

theorem b_step {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t)
    (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" base') t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT1 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.b_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.SignCached.b_call h hB hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.d1 ((VG.Proof.Ed448.X86.SignCached.out2_lo h).sub_left (args_lo _ (by decide))).symm)
      (by show 57 ≤ 2 ^ 64; decide)]

theorem k_step (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧
      Frame [fr (base s) K 57, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.k_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.SignCached.k_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := fr (base s) HASH 114) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 114 ≤ 2 ^ 64; decide)]

theorem m_step (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t) (ha : Shake.Args (base s) 8 (arg s) m) :
    WP isa (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧
      Frame [VG.Proof.Ed448.X86.SignCached.OUT2 s, SCR (arg s 7), Lo (base s)] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 57) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.m_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.X86.SignCached.m_call h hu hs) fun v ⟨hv, hf, ho⟩ => ⟨hv, ?_, ?_⟩
  · refine (hm.sub fun r hr => ⟨Lo (base s), by simp, ?_⟩).trans hf
    rw [List.mem_singleton.mp hr]; exact args_lo _ (by decide)
  · rw [ho, frame_bytes hm (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.d1 ((VG.Proof.Ed448.X86.SignCached.out2_lo h).sub_left (args_lo _ (by decide))).symm)
      (by show 57 ≤ 2 ^ 64; decide),
      frame_bytes hm (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 57 ≤ 2 ^ 64; decide),
      frame_bytes hm (D := fr (base s) S 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint_base _ (by decide) (by decide)))
      (by show 57 ≤ 2 ^ 64; decide)]

/-! ## The body -/

theorem body_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (hc : VG.Proof.Ed448.X86.SignCached.GCtx s g m t)
    (ha : Shake.Args (base s) 8 (arg s) m)
    (hkey : Spec.Ed448.bytesAt m ((arg s 2).setWidth 64) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57)) :
    WP isa (body base') t fun u => VG.Proof.Ed448.X86.SignCached.GCtx s g m u ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 114 = Spec.Ed448.sign
        (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57)
        (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        (Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have hcl : (arg s 4).toNat < 256 := by have := h.ctxlen; omega
  -- Disjointness of the values carried.
  have lS := lo_fr (base s) (d := S) (l := 57) (by decide) (by decide)
  have lK := lo_fr (base s) (d := K) (l := 57) (by decide) (by decide)
  have sS : (fr (base s) S 57).Disjoint (SCR (arg s 7)) := hk.fr_scr (by decide)
  have sK : (fr (base s) K 57).Disjoint (SCR (arg s 7)) := hk.fr_scr (by decide)
  have o1W : ∀ {d : Nat}, d + 114 ≤ 256 → ∀ r ∈ VG.Proof.Ed448.X86.SignCached.W s d, (VG.Proof.Ed448.X86.SignCached.OUT1 s).Disjoint r := fun hd =>
    VG.Proof.Ed448.X86.SignCached.dW h (VG.Proof.Ed448.X86.SignCached.out1_lo h) ((VG.Proof.Ed448.X86.SignCached.out_fr h hd).sub_left (VG.Proof.Ed448.X86.SignCached.out1_within s).sub) (VG.Proof.Ed448.X86.SignCached.out1_scr h)
  have o2W : ∀ {d : Nat}, d + 114 ≤ 256 → ∀ r ∈ VG.Proof.Ed448.X86.SignCached.W s d, (VG.Proof.Ed448.X86.SignCached.OUT2 s).Disjoint r := fun hd =>
    VG.Proof.Ed448.X86.SignCached.dW h (VG.Proof.Ed448.X86.SignCached.out2_lo h) ((VG.Proof.Ed448.X86.SignCached.out_fr h hd).sub_left (VG.Proof.Ed448.X86.SignCached.out2_within s).sub) (VG.Proof.Ed448.X86.SignCached.out2_scr h)
  have n57 : (57 : Nat) ≤ 2 ^ 64 := by decide
  unfold body
  -- `SHAKE256(seed, 114)` at `S`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.seed_ok h hc ha) fun t1 ⟨hc1, _, hs1⟩ => ?_)
  have hs1' : Spec.Ed448.bytesAt t1.mem ((base s).setWidth 64 + BitVec.ofNat 64 S) 114 =
      Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114 := hs1
  -- `s`, pruned in place; the prefix at `K`.
  refine WP.seq (WP.mono (hk.prune_ok hc1 (q := S) (by decide)) fun t2 ⟨hc2, hf2, hp2, _⟩ => ?_)
  rw [hs1'] at hp2
  have pf2 : Spec.Ed448.bytesAt t2.mem ((base s).setWidth 64 + BitVec.ofNat 64 K) 57 =
      (Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114).drop 57 := by
    rw [frame_bytes hf2 (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint _ (by decide) (by decide) (by decide))) n57,
      ← hs1', VG.Proof.Ed448.X86.SignCached.drop57, Offset.add_add]
    rfl
  -- The header.
  refine WP.seq (WP.mono (hk.hdr_ok hc2 ha (j := 4) (off := HASH) (by decide) hcl (by decide))
    fun t3 ⟨hc3, hf3, hh3, _⟩ => ?_)
  have sp3 := (frame_bytes hf3 (D := fr (base s) S 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57)
  have pf3 := (frame_bytes hf3 (D := fr (base s) K 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57).trans pf2
  -- The nonce's hash at `HASH`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.nonce_ok h hc3 ha hh3 pf3) fun t4 ⟨hc4, hf4, hn4⟩ => ?_)
  have sp4 := (frame_bytes hf4 (D := fr (base s) S 57)
    (VG.Proof.Ed448.X86.SignCached.dW h lS (Offset.disjoint _ (by decide) (by decide) (by decide)) sS) n57).trans sp3
  -- `r` into the second half of `out`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.r_step h hc4 ha) fun t5 ⟨hc5, hf5, hr5⟩ => ?_)
  have sp5 := (frame_bytes hf5 (D := fr (base s) S 57) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.fr_out2 h (by decide)) sS lS.symm) n57).trans sp4
  -- `R` into the first half.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.b_step h hB hc5 ha) fun t6 ⟨hc6, hf6, hR6⟩ => ?_)
  have sp6 := (frame_bytes hf6 (D := fr (base s) S 57) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.fr_out1 h (by decide)) sS lS.symm) n57).trans sp5
  have r6 := (frame_bytes hf6 (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.out12 s).symm (VG.Proof.Ed448.X86.SignCached.out2_scr h) (VG.Proof.Ed448.X86.SignCached.out2_lo h).symm) n57).trans hr5
  -- The header again.
  refine WP.seq (WP.mono (hk.hdr_ok hc6 ha (j := 4) (off := HASH) (by decide) hcl (by decide))
    fun t7 ⟨hc7, hf7, hh7, _⟩ => ?_)
  have sp7 := (frame_bytes hf7 (D := fr (base s) S 57) (VG.Proof.Ed448.X86.SignCached.d1 (Offset.disjoint _ (by decide) (by decide) (by decide)))
    n57).trans sp6
  have r7 := (frame_bytes hf7 (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.d1 ((VG.Proof.Ed448.X86.SignCached.out_fr h (by decide)).sub_left (VG.Proof.Ed448.X86.SignCached.out2_within s).sub)) n57).trans r6
  have R7 := (frame_bytes hf7 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.d1 ((VG.Proof.Ed448.X86.SignCached.out_fr h (by decide)).sub_left (VG.Proof.Ed448.X86.SignCached.out1_within s).sub)) n57).trans hR6
  -- The challenge's hash at `HASH`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.chal_ok h hc7 ha hh7 R7) fun t8 ⟨hc8, hf8, hn8⟩ => ?_)
  have sp8 := (frame_bytes hf8 (D := fr (base s) S 57)
    (VG.Proof.Ed448.X86.SignCached.dW h lS (Offset.disjoint _ (by decide) (by decide) (by decide)) sS) n57).trans sp7
  have r8 := (frame_bytes hf8 (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (o2W (by decide)) n57).trans r7
  have R8 := (frame_bytes hf8 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (o1W (by decide)) n57).trans R7
  -- `k` at `K`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.k_step h hc8 ha) fun t9 ⟨hc9, hf9, hk9⟩ => ?_)
  have sp9 := (frame_bytes hf9 (D := fr (base s) S 57)
    (VG.Proof.Ed448.X86.SignCached.d3 (Offset.disjoint _ (by decide) (by decide) (by decide)) sS lS.symm) n57).trans sp8
  have r9 := (frame_bytes hf9 (D := VG.Proof.Ed448.X86.SignCached.OUT2 s) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.fr_out2 h (by decide)).symm (VG.Proof.Ed448.X86.SignCached.out2_scr h) (VG.Proof.Ed448.X86.SignCached.out2_lo h).symm) n57).trans r8
  have R9 := (frame_bytes hf9 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.fr_out1 h (by decide)).symm (VG.Proof.Ed448.X86.SignCached.out1_scr h) (VG.Proof.Ed448.X86.SignCached.out1_lo h).symm) n57).trans R8
  -- `S` over `r`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.SignCached.m_step h hc9 ha) fun t10 ⟨hc10, hf10, hS10⟩ => ?_)
  have R10 := (frame_bytes hf10 (D := VG.Proof.Ed448.X86.SignCached.OUT1 s) (VG.Proof.Ed448.X86.SignCached.d3 (VG.Proof.Ed448.X86.SignCached.out12 s) (VG.Proof.Ed448.X86.SignCached.out1_scr h) (VG.Proof.Ed448.X86.SignCached.out1_lo h).symm) n57).trans R9
  -- The frame cleared.
  refine WP.mono (Whole.Ctx.zeroWords hc10 (start := 6) (count := 58) hk.frame (by decide)) fun u ⟨hu, hf, _⟩ =>
    ⟨hu, ?_⟩
  have keep := frame_bytes hf (D := VG.Proof.Ed448.X86.SignCached.OUT s) (VG.Proof.Ed448.X86.SignCached.d1 (VG.Proof.Ed448.X86.SignCached.out_fr h (d := 4 * 6) (l := 4 * 58) (by decide)))
    (by show 114 ≤ 2 ^ 64; decide)
  rw [keep, VG.Proof.Ed448.X86.SignCached.split114, R10, hS10, r9, hk9, hr5]
  have hn8' : Spec.Ed448.bytesAt t8.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        (Spec.Ed448.scalarBase (Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t4.mem
            ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114)) ++
          Spec.Ed448.bytesAt m ((arg s 2).setWidth 64) 57 ++
          Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := by
    rw [show Spec.Ed448.bytesAt t8.mem _ 114 = _ from hn8, ← hr5]
    rfl
  have hn4' : Spec.Ed448.bytesAt t4.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.hash (Spec.Ed448.bytesAt m ((arg s 3).setWidth 64) (arg s 4).toNat)
        ((Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114).drop 57 ++
          Spec.Ed448.bytesAt m ((arg s 5).setWidth 64) (arg s 6).toNat) := hn4
  rw [hn8', hn4', hkey]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ rfl (by rw [sp9]; exact hp2)

end

theorem body_nosp {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') : NoSp (body base') := by
  have z : NoSp (Impl.Ed448.X86.Shake.zeroState SC) := NoSp.of_all (by decide +kernel)
  have hdr : NoSp (.block (hdrAt 4 HASH)) := NoSp.of_all (by decide +kernel)
  have pr : NoSp (.block (pruneAt S)) := NoSp.of_all (by decide +kernel)
  have pd : NoSp (Impl.Ed448.X86.Shake.pad SC) := pad_nosp' (NoSp.of_all (by decide +kernel))
  have sqS : NoSp (Impl.Ed448.X86.Shake.squeeze SC S) := squeeze_nosp' (NoSp.of_all (by decide +kernel))
  have sqH : NoSp (Impl.Ed448.X86.Shake.squeeze SC HASH) := squeeze_nosp' (NoSp.of_all (by decide +kernel))
  have sh : NoSp seedHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqS))
  have nh : NoSp nonceHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
      (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqH)))))
  have ch : NoSp chalHash :=
    nosp_seq z (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
      (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
        (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
          (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
            (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel))) (nosp_seq pd sqH))))))
  have rr : NoSp (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) VG.Proof.Ed448.X86.SignCached.reduce_nosp
  have bb : NoSp (callWith baseArgs "vg_ed448_scalar_base" base') :=
    nosp_seq (NoSp.of_all (by decide +kernel)) hB.nosp
  have rk : NoSp (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) VG.Proof.Ed448.X86.SignCached.reduce_nosp
  have ma : NoSp (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) :=
    nosp_seq (NoSp.of_all (by decide +kernel)) VG.Proof.Ed448.X86.SignCached.mulAdd_nosp
  have wp : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact nosp_seq sh (nosp_seq pr (nosp_seq hdr (nosp_seq nh (nosp_seq rr (nosp_seq bb (nosp_seq hdr
    (nosp_seq ch (nosp_seq rk (nosp_seq ma wp)))))))))

theorem signCached_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') {s : State} (hp : scLocal.pre s) :
    WP isa (VG.Impl.Ed448.X86.SignCached.code base') s fun t => abiPreserved s t ∧ scLocal.post s t := by
  have h := VG.Proof.Ed448.X86.SignCached.facts hp
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := h.below; omega) (VG.Proof.Ed448.X86.SignCached.body_nosp hB)
    (WP.mono (VG.Proof.Ed448.X86.SignCached.body_ok h hB (push_ctx hp.1 hp.2.1 h.below) (args_val s 8) h.key) fun u ⟨hu, ho⟩ =>
      ⟨pop_abi (by decide) h.below hu (VG.Proof.Ed448.X86.SignCached.ret_out h), ?_⟩)
  change Spec.Ed448.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem ((arg s 0).setWidth 64) 114 = _
  rw [popped_mem]
  exact ho

end VG.Proof.Ed448.X86.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified`. -/
section

/-!
# Ed448 signing with a cached key on x86 (32-bit): constant time, and `Verified`

As for the public key: two runs from the same pointers, lengths and `esp`
set up the same arguments for every call, each callee is constant time under
its own contract (the sponge functions', `scalarReduceLocal`,
`scalarMulAddLocal` and `scalarBaseLocal`), and the blocks between the calls
address memory only through `esp` (or `scratch`, the same in both runs).
`signCached_verified`: for any `base` meeting `scalarBaseLocal`
(`CalleeOk`), `code base` meets `Spec.Ed448.signCachedContract X86.abi 280`.
-/

namespace VG.Proof.Ed448.X86.SignCached

open VG VG.X86 VG.Impl.Ed448.X86.SignCached
open VG.Impl.Ed448.X86.Shake (callWith hdrAt pruneAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Ctx.zeroWords)

variable {σ₁ σ₂ : State} {g₁ g₂ : Reg → BitVec 32}

theorem base_eq (hp : scLocal.pub σ₁ σ₂) : base σ₂ = base σ₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : scLocal.pub σ₁ σ₂) : VG.Proof.Ed448.X86.SignCached.scRd σ₂ = VG.Proof.Ed448.X86.SignCached.scRd σ₁ := by
  obtain ⟨e, _, a1, a2, a3, a4, a5, a6, _⟩ := hp
  simp only [VG.Proof.Ed448.X86.SignCached.scRd, VG.Proof.Ed448.X86.SignCached.SEED, VG.Proof.Ed448.X86.SignCached.PK, VG.Proof.Ed448.X86.SignCached.CTX, VG.Proof.Ed448.X86.SignCached.MSG, argAddr, e, a1, a2, a3, a4, a5, a6]

theorem wr_eq (hp : scLocal.pub σ₁ σ₂) : VG.Proof.Ed448.X86.SignCached.scWr σ₂ = VG.Proof.Ed448.X86.SignCached.scWr σ₁ := by
  obtain ⟨_, a0, _, _, _, _, _, _, a7⟩ := hp
  simp only [VG.Proof.Ed448.X86.SignCached.scWr, VG.Proof.Ed448.X86.SignCached.OUT, a0, a7]

theorem args₂ (hp : scLocal.pub σ₁ σ₂) : Shake.Args (base σ₁) 8 (arg σ₁) σ₂.mem := by
  obtain ⟨_, a0, a1, a2, a3, a4, a5, a6, a7⟩ := id hp
  intro i hi
  rw [← VG.Proof.Ed448.X86.SignCached.base_eq hp, args_val σ₂ 8 i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

abbrev Two₁ (σ₁ σ₂ : State) (g₁ g₂ : Reg → BitVec 32) :=
  Two (base σ₁) (VG.Proof.Ed448.X86.SignCached.scRd σ₁) (VG.Proof.Ed448.X86.SignCached.scWr σ₁) g₁ g₂ σ₁.mem σ₂.mem

section
variable {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : VG.Proof.Ed448.X86.SignCached.Facts σ₁) (hp : scLocal.pub σ₁ σ₂)

include h in
/-- Three to five equal slots, from the same values in both runs. -/
theorem eq_args {a b : State} (ea : a.gpr .esp = base σ₁) (eb : b.gpr .esp = base σ₁) {k : Nat} (hk6 : k ≤ 6)
    (hs : ∀ i < k, Whole.slots (base σ₁) a i = Whole.slots (base σ₁) b i) (ar aw br bw : List Region) :
    ∀ i < k, arg (a.callEntry.withRegions ar aw) i = arg (b.callEntry.withRegions br bw) i :=
  (VG.Proof.Ed448.X86.SignCached.kit h).args_eq ea eb hk6 hs ar aw br bw

include h hp in
theorem seed_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) seedHash (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have ha := args_val σ₁ 8
  have hb := VG.Proof.Ed448.X86.SignCached.args₂ hp
  have hsc := VG.Proof.Ed448.X86.SignCached.scr_at σ₁
  unfold seedHash
  exact RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide))
    (RelCT.seq (hk.first_ct ha hb hsc (src := .caller 1 0) (len := .const 57) (P := arg σ₁ 1) (N := 57)
      (show 1 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
      (.inr ⟨VG.Proof.Ed448.X86.SignCached.SEED σ₁, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.seed_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.seed_in σ₁) (whole _))
      h.seed (by taint_decide))
      (RelCT.seq (hk.padStep_ct ha hb hsc (pos := 57 % 136) (by decide) (by taint_decide))
        (hk.sqzStep_ct ha hb hsc (d := S) (by decide) (by decide) (by taint_decide))))

include h hp in
theorem nonce_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) nonceHash (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have ha := args_val σ₁ 8
  have hb := VG.Proof.Ed448.X86.SignCached.args₂ hp
  have hsc := VG.Proof.Ed448.X86.SignCached.scr_at σ₁
  have fa := hk.fr_addr (d := HASH) (by decide)
  have fk := hk.fr_addr (d := K) (by decide)
  unfold nonceHash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HASH) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.ctx_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .frame K) (len := .const 57)
    (P := base σ₁ + BitVec.ofNat 32 K) (N := 57) trivial trivial rfl rfl
    (by rw [fk]; exact .inl (frame_within _ (by decide)))
    (by rw [fk]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide))
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .caller 6 0) (P := arg σ₁ 5)
    (N := (arg σ₁ 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.msg_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

include h hp in
theorem chal_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) chalHash (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have ha := args_val σ₁ 8
  have hb := VG.Proof.Ed448.X86.SignCached.args₂ hp
  have hsc := VG.Proof.Ed448.X86.SignCached.scr_at σ₁
  have fa := hk.fr_addr (d := HASH) (by decide)
  unfold chalHash
  refine RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide)) ?_
  refine RelCT.seq (hk.first_ct ha hb hsc (src := .frame HASH) (len := .const 10)
    (P := base σ₁ + BitVec.ofNat 32 HASH) (N := 10) trivial trivial rfl rfl
    (by rw [fa]; exact .inl (frame_within _ (by decide)))
    (by rw [fa]; exact hk.away_fr (by decide) (by decide)) (hk.fr_fit (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 3 0) (len := .caller 4 0) (P := arg σ₁ 3)
    (N := (arg σ₁ 4).toNat) (show 3 < 8 by decide) (show 4 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.ctx_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.ctx_in σ₁) (whole _)) h.ctx
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 0 0) (len := .const 57) (P := arg σ₁ 0) (N := 57)
    (show 0 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_right _ (VG.Proof.Ed448.X86.SignCached.out_in σ₁), VG.Proof.Ed448.X86.SignCached.out1_within σ₁⟩)
    (hk.away_output (VG.Proof.Ed448.X86.SignCached.out_in σ₁) h.oc (VG.Proof.Ed448.X86.SignCached.out1_within σ₁)) (by have := h.out; omega)
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 2 0) (len := .const 57) (P := arg σ₁ 2) (N := 57)
    (show 2 < 8 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.pk_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.pk_in σ₁) (whole _)) h.pk
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  refine RelCT.seq (hk.next_ct ha hb hsc (src := .caller 5 0) (len := .caller 6 0) (P := arg σ₁ 5)
    (N := (arg σ₁ 6).toNat) (show 5 < 8 by decide) (show 6 < 8 by decide)
    (by rw [argVal_caller, BitVec.add_zero]) (by rw [argVal_caller, BitVec.add_zero])
    (.inr ⟨_, List.mem_append_left _ (VG.Proof.Ed448.X86.SignCached.msg_in σ₁), whole _⟩) (hk.away_input (VG.Proof.Ed448.X86.SignCached.msg_in σ₁) (whole _)) h.msg
    (Nat.mod_lt _ (by decide)) (by taint_decide)) ?_
  exact RelCT.seq (hk.padStep_ct ha hb hsc (Nat.mod_lt _ (by decide)) (by taint_decide))
    (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))

include h hp in
theorem r_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := VG.Proof.Ed448.X86.SignCached.RSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.r_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.r_setup h hc (VG.Proof.Ed448.X86.SignCached.args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
      (fun _ _ _ hc hs => VG.Proof.Ed448.X86.SignCached.r_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := VG.Proof.Ed448.X86.SignCached.eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.r_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.r_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include hB h hp in
theorem b_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith baseArgs "vg_ed448_scalar_base" base') (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := VG.Proof.Ed448.X86.SignCached.BSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.b_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.b_setup h hc (VG.Proof.Ed448.X86.SignCached.args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct hB.ok hB.ct (fun _ _ _ hc hs => VG.Proof.Ed448.X86.SignCached.b_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := VG.Proof.Ed448.X86.SignCached.eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.b_call h hB hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.b_call h hB hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include h hp in
theorem k_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.X86.scalarReduce) (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := VG.Proof.Ed448.X86.SignCached.KSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.k_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.k_setup h hc (VG.Proof.Ed448.X86.SignCached.args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarReduce_ok s h) Proof.Ed448.X86.scalarReduce_ct
      (fun _ _ _ hc hs => VG.Proof.Ed448.X86.SignCached.k_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := VG.Proof.Ed448.X86.SignCached.eq_args h ea eb (k := 3) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.k_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.k_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include h hp in
theorem m_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True)
      (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.X86.scalarMulAdd) (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) :=
  RelCT.seq (block_ct (Q := VG.Proof.Ed448.X86.SignCached.MSlots σ₁) (by taint_decide)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.m_setup h hc (args_val σ₁ 8)) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (VG.Proof.Ed448.X86.SignCached.m_setup h hc (VG.Proof.Ed448.X86.SignCached.args₂ hp)) fun _ hu => ⟨hu.1, hu.2.2⟩))
    (call_ct (fun s h => Proof.Ed448.X86.scalarMulAdd_ok s h) Proof.Ed448.X86.scalarMulAdd_ct
      (fun _ _ _ hc hs => VG.Proof.Ed448.X86.SignCached.m_ready h hc hs)
      (fun a b ea eb ha hb ar aw br bw => by
        have e := VG.Proof.Ed448.X86.SignCached.eq_args h ea eb (k := 5) (by decide) (fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
          exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm,
            ha.a3.trans hb.a3.symm, ha.a4.trans hb.a4.symm]) ar aw br bw
        exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide),
          e 3 (by decide), e 4 (by decide)⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.m_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
      (fun _ hc hs => WP.mono (VG.Proof.Ed448.X86.SignCached.m_call h hc hs) fun _ hv => ⟨hv.1, trivial⟩))

include hB h hp in
theorem body_ct :
    RelCT isa (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) (body base') (VG.Proof.Ed448.X86.SignCached.Two₁ σ₁ σ₂ g₁ g₂ fun _ => True) := by
  have hk := VG.Proof.Ed448.X86.SignCached.kit h
  have ha := args_val σ₁ 8
  have hb := VG.Proof.Ed448.X86.SignCached.args₂ hp
  have hcl : (arg σ₁ 4).toNat < 256 := by have := h.ctxlen; omega
  have hdr := hk.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 4) (off := HASH) (by decide) hcl (by decide)
    (by taint_decide)
  unfold body
  exact (VG.Proof.Ed448.X86.SignCached.seed_ct h hp).seq ((hk.prune_ct (q := S) (by decide) (by taint_decide)).seq (hdr.seq
    ((VG.Proof.Ed448.X86.SignCached.nonce_ct h hp).seq ((VG.Proof.Ed448.X86.SignCached.r_ct h hp).seq ((VG.Proof.Ed448.X86.SignCached.b_ct hB h hp).seq (hdr.seq ((VG.Proof.Ed448.X86.SignCached.chal_ct h hp).seq ((VG.Proof.Ed448.X86.SignCached.k_ct h hp).seq
    ((VG.Proof.Ed448.X86.SignCached.m_ct h hp).seq (block_ct (by taint_decide)
      (fun _ hc _ => WP.mono (Whole.Ctx.zeroWords hc (start := 6) (count := 58) hk.frame (by decide))
        fun _ hu => ⟨hu.1, trivial⟩)
      (fun _ hc _ => WP.mono (Whole.Ctx.zeroWords hc (start := 6) (count := 58) hk.frame (by decide))
        fun _ hu => ⟨hu.1, trivial⟩)))))))))))

end

theorem signCached_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    ConstantTime isa scLocal.pre scLocal.pub (VG.Impl.Ed448.X86.SignCached.code base') := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have c₂ := push_ctx p₂.1 p₂.2.1 (VG.Proof.Ed448.X86.SignCached.facts p₂).below
  rw [VG.Proof.Ed448.X86.SignCached.base_eq hp, VG.Proof.Ed448.X86.SignCached.rd_eq hp, VG.Proof.Ed448.X86.SignCached.wr_eq hp] at c₂
  exact ⟨(VG.Proof.Ed448.X86.SignCached.body_ct hB (VG.Proof.Ed448.X86.SignCached.facts p₁) hp _ _ _ _ _ _
    ⟨⟨push_ctx p₁.1 p₁.2.1 (VG.Proof.Ed448.X86.SignCached.facts p₁).below, trivial⟩, ⟨c₂, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The shared contract -/

def scWide : Contract isa := { VG.Proof.Ed448.X86.SignCached.scLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 114⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let ctx : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let msg : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scr : Region := ⟨(arg s 7).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, ctx, msg] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint ctx ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 114 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
      (arg s 7).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
      Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57) ∧
      (arg s 4).toNat ≤ 255 }

theorem scWide_pre (s : State) (h : scWide.pre s) :
    scLocal.pre (s.withRegions (VG.Proof.Ed448.X86.SignCached.scRd s) (VG.Proof.Ed448.X86.SignCached.scWr s)) := by
  obtain ⟨_, _, a1, a2, a3, a4, a5, a6, ko, a8, a9, a10, a11, a12, a13, a14, ks, kp, kx, km, kc,
    b1, b2, b3, b4, b5, b6, nb, b8, b9, b10⟩ := h
  simp only [VG.Proof.Ed448.X86.SignCached.scLocal, VG.Proof.Ed448.X86.SignCached.scRd, VG.Proof.Ed448.X86.SignCached.scWr, VG.Proof.Ed448.X86.SignCached.SEED, VG.Proof.Ed448.X86.SignCached.PK, VG.Proof.Ed448.X86.SignCached.CTX, VG.Proof.Ed448.X86.SignCached.MSG, VG.Proof.Ed448.X86.SignCached.OUT, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, below,
    Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, a1, a2, a3, a4, a5, a6, ko, a8, a9, a10, a11, a12, a13, a14, ks, kp, kx, km, kc,
    b1, b2, b3, b4, b5, b6, nb, b8, b9, b10⟩

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey VG.Proof.Ed448.X86.SignCached.satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [VG.Proof.Ed448.X86.SignCached.satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, the arguments at `0x9004`, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3039 then VG.Proof.Ed448.X86.SignCached.satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else if a = 0x900d then 0x30 else
    if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else if a = 0x9022 then 0x01 else 0

theorem sat_seed : Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem 0x2000 57 = VG.Proof.Ed448.X86.SignCached.satSeed := by
  unfold VG.Proof.Ed448.X86.SignCached.satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold VG.Proof.Ed448.X86.SignCached.satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem 0x3000 57 = VG.Proof.Ed448.X86.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, VG.Proof.Ed448.X86.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed448.X86.SignCached.satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3039 from by omega, ite_true,
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk' : Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem 0x2000 57) := by
  rw [VG.Proof.Ed448.X86.SignCached.sat_seed, VG.Proof.Ed448.X86.SignCached.sat_key]
  rfl

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86.SignCached.satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩, ⟨0x9004, 32⟩]

theorem sat_pk : Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem ((arg VG.Proof.Ed448.X86.SignCached.satState 2).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt VG.Proof.Ed448.X86.SignCached.satMem ((arg VG.Proof.Ed448.X86.SignCached.satState 1).setWidth 64) 57) := by
  have a1 : arg VG.Proof.Ed448.X86.SignCached.satState 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Ed448.X86.SignCached.satState 2 = 0x3000 := by decide
  rw [a1, a2]
  exact VG.Proof.Ed448.X86.SignCached.sat_pk'

theorem sat : ∃ s, (Spec.Ed448.signCachedContract X86.abi 280).pre s := by
  refine ⟨VG.Proof.Ed448.X86.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.Proof.Ed448.X86.SignCached.satState]
    sig_and_intros
    all_goals try exact VG.Proof.Ed448.X86.SignCached.sat_pk
    all_goals decide +kernel

theorem scWide_implies : scWide.Implies (Spec.Ed448.signCachedContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.SignCached.scWide, VG.Proof.Ed448.X86.SignCached.scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.SignCached.scWide, VG.Proof.Ed448.X86.SignCached.scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.SignCached.scWide, VG.Proof.Ed448.X86.SignCached.scLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  sat := VG.Proof.Ed448.X86.SignCached.sat

theorem signCached_verified {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    Verified X86.target (VG.Impl.Ed448.X86.SignCached.code base') (Spec.Ed448.signCachedContract X86.abi 280) := by
  have hsat := scWide_implies.sat_left
  have satLocal : ∃ s, scLocal.pre s := hsat.elim fun s h => ⟨_, VG.Proof.Ed448.X86.SignCached.scWide_pre s h⟩
  have verifiedLocal : Verified X86.target (VG.Impl.Ed448.X86.SignCached.code base') VG.Proof.Ed448.X86.SignCached.scLocal :=
    Verified.of_correct (fun _ h => VG.Proof.Ed448.X86.SignCached.signCached_ok hB h) (VG.Proof.Ed448.X86.SignCached.signCached_ct hB) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal VG.Proof.Ed448.X86.SignCached.scRd VG.Proof.Ed448.X86.SignCached.scWr VG.Proof.Ed448.X86.SignCached.scWide_pre
    ?_ ?_ ?_ ?_ hsat) VG.Proof.Ed448.X86.SignCached.scWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.SignCached.scRd, VG.Proof.Ed448.X86.SignCached.scWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.SignCached.scWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [VG.Proof.Ed448.X86.SignCached.scWide, VG.Proof.Ed448.X86.SignCached.scLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86.SignCached

end
