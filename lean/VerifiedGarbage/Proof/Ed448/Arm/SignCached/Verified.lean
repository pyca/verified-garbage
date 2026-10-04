import VerifiedGarbage.Proof.Ed448.Arm.SignCached.CT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Ed448 signing with a cached public key on ARMv7: the whole function

`signLocal`, the contract the proof is written against; `signCached_ok`, the
frame (`Whole.wrap_ok`) around the body; `signCached_ct`, constant time
(`Whole.wrap_ct`, from `body_ct`); and `signCached_verified`, against
`Spec.Ed448.signCachedContract Arm.abi 280`, given the reference ladder's
agreement with the specification (`BaseLadderOk`), which only the
registration file supplies.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok Whole.wrap_ct
  Whole.originalWord Whole.Ctx)
open VG.Proof.Ed448 (BaseLadderOk)

/-- `vg_ed448_sign_cached(out = r0, seed = r1, pk = r2, context = r3,
ctxlen = [sp], message = [sp, #4], len = [sp, #8], scratch = [sp, #12])`, with
280 bytes of stack. -/
def signLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 114⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let msg : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 3), 8192⟩
    let args : Region := ⟨State.addr s.sp, 16⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed, pk, ctx, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint scr ∧ seed.Disjoint out ∧ seed.Disjoint scr ∧ pk.Disjoint out ∧ pk.Disjoint scr ∧
      ctx.Disjoint out ∧ ctx.Disjoint scr ∧ msg.Disjoint out ∧ msg.Disjoint scr ∧
      args.Disjoint out ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧
      stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 114 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧
      (stackArg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat ≤ 255 ∧
      Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2 ∧ stackArg s 3 = stackArg t 3

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
    Whole.base s⟩

section
variable {s : State} (h : signLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_top : s.sp.toNat + 16 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := h
  exact ht

theorem original_args : (lay s).ORIG = ⟨State.addr s.sp, 16⟩ := by
  unfold Lay.ORIG lay
  rw [Whole.base_addr (entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hs := stack_eq h
  obtain ⟨_, hw, _, _, _, _, _, _, _, _, _, _, _, ko, _, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hs]
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok : (lay s).Ok := by
  have hb := entry_below h
  have ht := entry_top h
  have ho := original_args h
  have hs : (lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, oc, eo, ec, po, pc, xo, xc, mo, mc, ao, ac, ko, ke, kp, kx, km, kc, no, ne, np, nx, nm, nc,
    _, _, cl, _⟩ := h
  refine ⟨?_, by change (stackArg s 0).toNat < 256; omega, oc, eo, ec, po, pc, xo, xc, mo, mc,
    by rw [ho]; exact ao, by rw [ho]; exact ac, by rw [hs]; exact ko, by rw [hs]; exact ke,
    by rw [hs]; exact kp, by rw [hs]; exact kx, by rw [hs]; exact km, by rw [hs]; exact kc,
    no, ne, np, nx, nm, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 296 ≤ 2 ^ 32
  omega

theorem entry_regions : (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.SEED, Lay.PK, Lay.CTX, Lay.MSG, Lay.OUT, Lay.SCR,
    Lay.ARGS, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  rw [(entry_regions h).1, (entry_regions h).2]
  exact hc

/-- The caller's stack argument `j - 6`, at `E + 248 + 4 j`, where the caller put it. -/
theorem caller_word {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) {j : Nat} (hj : 10 ≤ j) (hj' : j < 12) :
    p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = stackArg s (j - 8) := by
  have hb := entry_below h
  have ht := entry_top h
  have hf := Whole.saved_frame hb hp
  have hbt := Whole.base_top hb
  have ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j) =
      State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 8))) := by
    rw [addr_add (by omega), Whole.base_addr hb, show 248 + 4 * j = 280 + 4 * (j - 8) by omega,
      ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
      BitVec.sub_add_cancel]
  rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j), 4⟩) (Region.contains_self _ _)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), ea]
  rfl

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  have hb := entry_below h
  have ht := entry_top h
  intro j hj
  obtain ⟨hj12, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega) hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, lay, stackArg, stackArgAddr] using hw
  · have he : j = 10 ∨ j = 11 := by omega
    rcases he with rfl | rfl
    · exact caller_word h hp (by decide) (by decide)
    · exact caller_word h hp (by decide) (by decide)

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  have ht := entry_top h
  intro j hj h4
  refine ⟨⟨State.addr s.sp, 16⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega)]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega) (by omega)

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, ke, kp, kx, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ke.symm
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 16) (by decide)

theorem entry_key {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed448.bytesAt p.mem (State.addr (lay s).pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (lay s).seed) 57) := by
  have hk : Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  have hf := Whole.saved_frame (entry_below h) hp
  have hp' := entry_input h hf (r := ⟨State.addr (s.gpr .r2), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have hs' := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  change Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r2)) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r1)) 57)
  simp only at hp' hs'
  rw [hp', hs']
  exact hk

end

theorem body_noFrames : body.noFrames = true := by
  simp only [body, seedHash, prune, nonceHash, chalHash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, reduce_noFrames,
    base_noFrames, mulAdd_noFrames]
  rfl

theorem signCached_ok (hl : BaseLadderOk) {s : State} (h : signLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ signLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 6 ≤ 6) (entry_below h)
    (by have := entry_top h; omega) (entry_read h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) (stackArg s 2).toNat))
    (fun p hp => WP.mono (body_ok hl (entry_ctx h hp) (lay_ok h) (entry_args h hp) (entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have e1 := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have e3 := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega)
  have e5 := entry_input h hf (r := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 2).toNat ≤ 2 ^ 64; have := (stackArg s 2).isLt; omega)
  change Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r0)) 114 = _
  simp only at e1 e3 e5
  rw [hp, e1, e3, e5]

theorem lay_eq {s t : State} (hp : signLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2, a3⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2, a3]

theorem signCached_ct (hl : BaseLadderOk) : ConstantTime isa signLocal.pre signLocal.pub code := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => entry_below hs)
    (fun _ hs => by have := entry_top hs; omega) (fun _ hs => entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok hl (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_key hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    exact ⟨(body_ct hl (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The contract -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, `scratch`'s address `0x10000` as the fourth
argument on the stack, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a = 0x900E then 1 else if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  have hne : (0x2000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  simp only [satMem, hne, ↓reduceIte, ha, show 0x2000 + i < 0x3000 from by omega, true_or]

theorem sat_key : Spec.Ed448.bytesAt satMem 0x3000 57 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    have hne : (0x3000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
      have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, satMem, hne, ↓reduceIte, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk : Spec.Ed448.bytesAt satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt satMem 0x2000 57) := by
  rw [sat_seed, sat_key]
  rfl

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract Arm.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, satState]
    sig_and_intros
    all_goals try exact sat_pk
    all_goals decide +kernel

theorem sign_implies : signLocal.Implies (Spec.Ed448.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [signLocal, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := sat

/-- `vg_ed448_sign_cached` on ARMv7, given the reference ladder's agreement
with the specification. -/
theorem signCached_verified (hl : BaseLadderOk) :
    Verified Arm.target code (Spec.Ed448.signCachedContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok hl h) (signCached_ct hl) (.refl sign_implies.sat_left))
    sign_implies

end VG.Proof.Ed448.Arm.SignCached
