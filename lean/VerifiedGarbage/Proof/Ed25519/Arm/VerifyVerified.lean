import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTRhs
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTRoot
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTPoints`. -/
section
/-! The strict equation has identical traces for identical public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EquationCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7776 = a ∧ tablePoint s.mem b 7904 = r

theorem verifyLhs_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyLhs (fun s t => RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) s ∧
        RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) t) := by
  apply ctBoth
  · exact (verifyLhs_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr⟩
    refine WP.mono (verifyLhs_ok hp.ctx hl) fun t ⟨tk, tl, tp, ta, tr⟩ => ?_
    exact ⟨hp.keep tk, tl, ta.trans ha, tr.trans hr,
      tp.trans (congrArg (fun bs => Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE bs) Spec.Ed25519.basePoint) hp.sBytes)⟩

theorem verifyEquationPoints_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyEquationPoints (fun _ _ => True) :=
  RelCT.seq (verifyLhs_public_ct m b pk sig challenge a r) (verifyRhs_ct m b pk sig challenge a r _)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeSupport`. -/
section

/-! Merged from `Proof.Ed25519.Arm.PointDecodeCT`. -/
section
/-! Strict point decoding leaks only its public encoded bytes and pointers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def DecodeCTPre (base ptr : BitVec 32) (bs : List Byte) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩ ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem pointDecode_ct (base ptr : BitVec 32) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t) pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t)
      pointDecodeLoad (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base ptr bs s) :
      WP isa pointDecodeLoad s fun t => RecoverCTPre base b y t ∧
        t.z = decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P) := by
    obtain ⟨hc, hl, hp, hf, hr, hsep, hbs⟩ := h
    refine WP.mono (pointDecodeLoad_ok hc hl hp hf hr hsep) fun t ⟨kt, lt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.ctx hc, lt, ?_, ?_⟩, ?_⟩
    · rw [tb, hbs]
    · rw [ty, hbs]
    · rw [tz, hbs]
  rw [pointDecode]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (recoverPoint_ct base b y).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Untrusted: the loop decoding `A` and `R` is determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem VerifyPublic.inBytes {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) {j : Nat} (hj : j < 2) :
    Spec.Ed25519.bytesAt s.mem (State.addr (inPtr pk sig j)) 32 =
      Spec.Ed25519.bytesAt m (State.addr (inPtr pk sig j)) 32 := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact h.pkBytes
  · exact h.rBytes

theorem VerifyPublic.decOk_eq {m : Mem} {b pk sig challenge : BitVec 32} {s : State}
    (h : VerifyPublic m b pk sig challenge s) : decOk s.mem pk sig 2 = decOk m pk sig 2 := by
  rw [decOk_two, decOk_two]
  unfold inPoint
  rw [h.inBytes (j := 0) (by decide), h.inBytes (j := 1) (by decide)]

/-- Before the decoding `k`, from some state before the loop with the public inputs. -/
def DecCT (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  ∃ s₀, VerifyPublic m b pk sig challenge s₀ ∧ DecAt s₀ b pk sig k s

theorem DecCT.r0 {m : Mem} {b pk sig challenge : BitVec 32} {k : Nat} {s : State}
    (h : DecCT m b pk sig challenge k s) : s.gpr .r0 = b := by
  obtain ⟨_, hp, hd⟩ := h
  exact (hp.ctx.keep hd.keep).ctx.r0

/-- What the iteration `k` needs public, after the pointer's load, and after the decoding. -/
def BodyCT (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ lw s.mem b DPTR = inPtr pk sig k ∧
    lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

def LoadedCT (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ s.gpr .r12 = inPtr pk sig k ∧
    lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

def DecodedCT (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ lw s.mem b DTAB = BitVec.ofNat 32 (7776 + 128 * k)

theorem DecCT.body {m : Mem} {b pk sig challenge : BitVec 32} {k : Nat} {s : State}
    (h : DecCT m b pk sig challenge k s) (hk : k < 2) : BodyCT m b pk sig challenge k s := by
  obtain ⟨_, hp, hd⟩ := h
  exact ⟨hp.keep hd.keep, hd.lim, hd.ptr hk, hd.tab⟩

theorem decodeLoad_ct (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) :
    CT (fun x y => BodyCT m b pk sig challenge k x ∧ BodyCT m b pk sig challenge k y)
      (.block [.ldr .r12 .r0 DPTR])
      (fun x y => LoadedCT m b pk sig challenge k x ∧ LoadedCT m b pk sig challenge k y) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
  · intro s ⟨hp, hl, hptr, htab⟩
    refine ldrLow_ok hp.ctx.ctx (d := DPTR) (by decide) .r12 fun t ht => WP.block_nil ?_
    have kt : VerifyKeep b s t := VerifyKeep.of_rest (ht.rest (ws := [.r12]) (by decide)) (by decide) ht.mem
    exact ⟨hp.keep kt, by rw [ht.mem]; exact hl, by rw [ht.gpr]; exact hptr, by rw [ht.mem]; exact htab⟩

theorem pointDecode_public_ct (m : Mem) (b pk sig challenge : BitVec 32) {k : Nat} (hk : k < 2) :
    CT (fun x y => LoadedCT m b pk sig challenge k x ∧ LoadedCT m b pk sig challenge k y) pointDecode
      (fun x y => DecodedCT m b pk sig challenge k x ∧ DecodedCT m b pk sig challenge k y) := by
  have pre (x : State) (h : LoadedCT m b pk sig challenge k x) :
      DecodeCTPre b (inPtr pk sig k) (Spec.Ed25519.bytesAt m (State.addr (inPtr pk sig k)) 32) x := by
    have hi := h.1.ctx.input hk
    exact ⟨h.1.ctx.ctx, h.2.1, h.2.2.1, hi.fit, hi.readable, hi.separate, h.1.inBytes hk⟩
  apply ctBoth
  · exact (pointDecode_ct b (inPtr pk sig k) _).mono (fun x y h => ⟨pre x h.1, pre y h.2⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, hr, htab⟩
    have hi := hp.ctx.input hk
    refine WP.mono (pointDecode_ok hp.ctx.ctx hl hr hi.fit hi.readable hi.separate) fun t ht => ?_
    refine ⟨hp.keep (VerifyKeep.of_decode ht.1), ht.2.1, ?_⟩
    rw [← htab]
    exact ht.1.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) (by decide)

theorem decodeNext_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (k : Nat) :
    CT (fun x y => DecodedCT m b pk sig challenge k x ∧ DecodedCT m b pk sig challenge k y)
      (.block decodeNext) (fun _ _ => True) := by
  rw [decodeNext_eq]
  have head : CT (fun x y => DecodedCT m b pk sig challenge k x ∧ DecodedCT m b pk sig challenge k y)
      (.block ([.ldr .r3 .r0 DOK, .dp .and .r3 .r3 (.reg .r9), .str .r3 .r0 DOK, .ldr .r12 .r0 DTAB,
        .dp .add .r12 .r0 (.reg .r12)] : List Instr))
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = b + BitVec.ofNat 32 (7776 + 128 * k)) ∧
        (y.gpr .r0 = b ∧ y.gpr .r12 = b + BitVec.ofNat 32 (7776 + 128 * k))) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
    · intro s ⟨hp, _, htab⟩
      have cs := hp.ctx.ctx
      refine ldrLow_ok cs (d := DOK) (by decide) .r3 fun u1 h1 => ?_
      have c1 : Ctx b u1 := cs.of_rest (h1.rest (ws := [.r3]) (by decide)) (by decide)
      refine wp_dp (op2_reg _ _) fun u2 h2 => ?_
      have c2 : Ctx b u2 := c1.of_rest (h2.rest (ws := [.r3]) (by decide)) (by decide)
      refine strLow_ok c2 (d := DOK) (by decide) .r3 fun u3 h3 => ?_
      have c3 : Ctx b u3 := c2.of_rest (h3.rest []) (by decide)
      refine ldrLow_ok c3 (d := DTAB) (by decide) .r12 fun u4 h4 => ?_
      have c4 : Ctx b u4 := c3.of_rest (h4.rest (ws := [.r12]) (by decide)) (by decide)
      refine wp_dp (op2_reg _ _) fun u5 h5 => WP.block_nil ⟨?_, ?_⟩
      · exact (c4.of_rest (h5.rest (ws := [.r12]) (by decide)) (by decide)).r0
      · rw [h5.gpr]
        change u4.gpr .r0 + u4.gpr .r12 = _
        rw [h4.gpr, h4.other _ (by decide), c3.r0, h3.mem, h2.mem, h1.mem,
          lw_write _ _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), htab]
  refine ctBlockAppend head ?_
  apply ctRegs [.r0, .r12] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem decodeBody_public_ct (m : Mem) (b pk sig challenge : BitVec 32) {k : Nat} (hk : k < 2) :
    CT (fun x y => BodyCT m b pk sig challenge k x ∧ BodyCT m b pk sig challenge k y) decodeBody
      (fun _ _ => True) := by
  rw [decodeBody]
  exact RelCT.seq (decodeLoad_ct m b pk sig challenge k)
    (RelCT.seq (pointDecode_public_ct m b pk sig challenge hk) (decodeNext_public_ct m b pk sig challenge k))

theorem decodeBody_dec {m : Mem} {b pk sig challenge : BitVec 32} {k : Nat} (hk : k < 2) {s : State}
    (h : DecCT m b pk sig challenge k s) :
    WP isa decodeBody s fun t => DecCT m b pk sig challenge (k + 1) t ∧ t.z = decide (k = 1) := by
  obtain ⟨s₀, hp, hd⟩ := h
  exact WP.mono (decodeBody_ok hp.ctx hk hd) fun t ⟨ht, zt⟩ => ⟨⟨s₀, hp, ht⟩, zt⟩

theorem decodeLoop_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun x y => DecCT m b pk sig challenge 0 x ∧ DecCT m b pk sig challenge 0 y) (.loop decodeBody .ne)
      (fun x y => DecCT m b pk sig challenge 2 x ∧ DecCT m b pk sig challenge 2 y) := by
  refine (RelCT.loop (M := isa) (I := fun n x y => ∃ k, k + n = 2 ∧ k < 2 ∧ DecCT m b pk sig challenge k x ∧
      DecCT m b pk sig challenge k y) ?_ 2).mono (fun x y h => ⟨0, rfl, by decide, h.1, h.2⟩) (fun _ _ h => h)
  intro n
  have step (k : Nat) (hk : k < 2) := ((decodeBody_public_ct m b pk sig challenge hk).mono
    (fun x y (h : DecCT m b pk sig challenge k x ∧ DecCT m b pk sig challenge k y) => ⟨h.1.body hk, h.2.body hk⟩)
    (fun _ _ h => h)).wp fun x y h => ⟨decodeBody_dec hk h.1, decodeBody_dec hk h.2⟩
  rcases n with _ | _ | _ | n
  · exact RelCT.of_false fun _ _ ⟨k, hkn, hk, _⟩ => by omega
  · refine ((step 1 (by decide)).mono (fun x y ⟨k, hkn, _, hx, hy⟩ => by
      obtain rfl : k = 1 := by omega
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun _ => ⟨hx, hy⟩, fun he => ?_⟩
    · show some (!x.z) = some (!y.z)
      rw [zx, zy]
    · have e : some (!x.z) = some true := he
      rw [zx] at e
      cases e
  · refine ((step 0 (by decide)).mono (fun x y ⟨k, hkn, _, hx, hy⟩ => by
      obtain rfl : k = 0 := by omega
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun he => ?_, fun _ => ⟨1, by omega, 1, rfl, by decide, hx, hy⟩⟩
    · show some (!x.z) = some (!y.z)
      rw [zx, zy]
    · have e : some (!x.z) = some false := he
      rw [zx] at e
      cases e
  · exact RelCT.of_false fun _ _ ⟨k, hkn, hk, _⟩ => by omega

/-- After the test of `DOK`: the branch, and the decoded points. -/
def TestedCT (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ VG.Arm.eval .ne s = some (decOk m pk sig 2) ∧
    ∀ j < 2, ∀ p, inPoint m pk sig j = some p → tablePoint s.mem b (7776 + 128 * j) = p

theorem okTest_dec {m : Mem} {b pk sig challenge : BitVec 32} {s : State} (h : DecCT m b pk sig challenge 2 s) :
    WP isa (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)]) s (TestedCT m b pk sig challenge) := by
  obtain ⟨s₀, hp, ha⟩ := h
  refine ldrLow_ok (hp.ctx.keep ha.keep).ctx (d := DOK) (by decide) .r9 fun c hc =>
    wp_cmp (op2_imm (by decide)) fun d hd hz => WP.block_nil ?_
  have md : d.mem = s.mem := by rw [hd.mem, hc.mem]
  have kd : VerifyKeep b s₀ d := ha.keep.trans (VerifyKeep.of_rest ((hc.rest (ws := [.r9]) (by decide)).trans
    (hd.rest _)) (by decide) md)
  refine ⟨hp.keep kd, by rw [md]; exact ha.lim, ?_, fun j hj p hj' => ?_⟩
  · show some (!d.z) = _
    rw [hz, hc.gpr, ha.ok, hp.decOk_eq]
    cases decOk m pk sig 2 <;> rfl
  · rw [md]
    refine ha.pts j hj p ?_
    unfold inPoint at hj' ⊢
    rw [hp.inBytes hj]
    exact hj'

theorem verifyDecode_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) verifyDecode (fun _ _ => True) := by
  have start : CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) (.block decodeStart)
      (fun x y => DecCT m b pk sig challenge 0 x ∧ DecCT m b pk sig challenge 0 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
    · intro s ⟨hp, hl⟩
      exact WP.mono (decodeStart_ok hp.ctx hl) fun t ht => ⟨s, hp, ht⟩
  have test : CT (fun x y => DecCT m b pk sig challenge 2 x ∧ DecCT m b pk sig challenge 2 y)
      (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)])
      (fun x y => TestedCT m b pk sig challenge x ∧ TestedCT m b pk sig challenge y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.r0.trans h.2.r0.symm
    · exact fun s h => okTest_dec h
  rw [verifyDecode, decodeBoth]
  refine RelCT.seq (RelCT.seq start (decodeLoop_ct m b pk sig challenge)) (RelCT.seq test (RelCT.ite ?_ ?_ ?_))
  · exact fun _ _ h => h.1.2.2.1.trans h.2.2.2.1.symm
  · cases ha : inPoint m pk sig 0 with
    | none =>
      exact RelCT.of_false fun x y hh => by
        have e : some (decOk m pk sig 2) = some true := hh.1.1.2.2.1.symm.trans hh.2
        rw [decOk_two, ha] at e
        cases e
    | some a =>
      cases hr : inPoint m pk sig 1 with
      | none =>
        exact RelCT.of_false fun x y hh => by
          have e : some (decOk m pk sig 2) = some true := hh.1.1.2.2.1.symm.trans hh.2
          rw [decOk_two, ha, hr] at e
          cases e
      | some r =>
        refine (verifyEquationPoints_ct m b pk sig challenge a r).mono ?_ (fun _ _ h => h)
        intro x y ⟨⟨hx, hy⟩, _⟩
        exact ⟨⟨hx.1, hx.2.1, hx.2.2.2 0 (by decide) a ha, hx.2.2.2 1 (by decide) r hr⟩,
          ⟨hy.1, hy.2.1, hy.2.2.2 0 (by decide) a ha, hy.2.2.2 1 (by decide) r hr⟩⟩
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTBody`. -/
section

/-! Merged from `Proof.Ed25519.Arm.VerifyCTScalar`. -/
section
/-! Canonical scalar checking loads through the public signature pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block verifyScalar) (fun _ _ => True) := by
  have head : CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block (loadHeader 8164 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · intro s hc
      rw [WP.block_append_iff]
      refine WP.mono (loadHeader_ok hc.ctx 8164 (by decide)) fun u ⟨ur, um, up⟩ => ?_
      refine WP.mono (addInput32_ok u) fun t ⟨tr, _, tp⟩ => ?_
      exact ⟨(tr.gpr _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.ctx.r0), by rw [tp, up, hc.sigHeader]⟩
  have tail : CT (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32))
      (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr))) (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  simpa only [verifyScalar, List.append_assoc] using ctBlockAppend head tail

theorem verifyScalar_public_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block verifyScalar) (fun s t =>
        (VerifyPublic m b pk sig challenge s ∧ s.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L)) ∧
        (VerifyPublic m b pk sig challenge t ∧ t.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L))) := by
  apply ctBoth
  · exact (verifyScalar_ct b pk sig challenge).mono (fun _ _ h => ⟨h.1.ctx, h.2.ctx⟩) (fun _ _ h => h)
  · intro s hs
    refine WP.mono (verifyScalar_ok hs.ctx) fun t ⟨tk, tz⟩ => ?_
    exact ⟨hs.keep tk, tz.trans (congrArg (fun bs => decide (Spec.Ed25519.decodeLE bs < Spec.Ed25519.L)) hs.sBytes)⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete strict verifier leaks only its declared public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem verifyInit_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block initFields) (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
        (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.ctx.ctx.r0.trans h.2.ctx.ctx.r0.symm
  · intro s hs
    refine WP.mono (initFields_ok hs.ctx.ctx) fun t ⟨tk, tl, _⟩ => ?_
    exact ⟨hs.keep (VerifyKeep.of_keep tk), tl⟩

theorem verifyBody_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      verifyBody (fun _ _ => True) := by
  refine RelCT.seq (verifyScalar_public_ct m b pk sig challenge) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (RelCT.seq (verifyInit_ct m b pk sig challenge) (verifyDecode_ct m b pk sig challenge)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! The verifier's ABI wrapper preserves the public input relation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

structure VerifyWrapPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  pre : verifyLocal.pre s
  r0 : s.gpr .r0 = pk
  r1 : s.gpr .r1 = sig
  r2 : s.gpr .r2 = challenge
  r3 : s.gpr .r3 = b
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem verifySetup_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
      (.block verifySetup) (fun x y => VerifyPublic m b pk sig challenge x ∧ VerifyPublic m b pk sig challenge y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2, .r3] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.r0.trans h.2.r0.symm
    · exact h.1.r1.trans h.2.r1.symm
    · exact h.1.r2.trans h.2.r2.symm
    · exact h.1.r3.trans h.2.r3.symm
  · intro s h
    have hp := VerifyPre.of h.pre
    refine WP.mono (verifySetup_ok hp) fun t ⟨tc, _, _, _, tf⟩ => ?_
    have tc' : VerifyContext b pk sig challenge t := by rw [h.r0, h.r1, h.r2, h.r3] at tc; exact tc
    have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
        Spec.Ed25519.bytesAt t.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => tf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr, h.r3]
      exact hd
    exact ⟨tc', (bytes pk 32 (by decide) tc'.pkInput.separate).trans h.pkBytes,
      (bytes sig 64 (by decide) tc'.sigInput.separate).trans h.sigBytes,
      (bytes challenge 64 (by decide) tc'.challengeInput.separate).trans h.challengeBytes⟩

theorem verify_ct_of_body
    (bodyCT : ∀ (m : Mem) (b pk sig challenge : BitVec 32),
      CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
        verifyBody (fun _ _ => True)) :
    ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have hct (m : Mem) (b pk sig challenge : BitVec 32) :
      CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
        verifyEquation (fun _ _ => True) := by
    have hb := (bodyCT m b pk sig challenge).wpDep (fun x y h => ⟨verifyBody_ok h.1.ctx, verifyBody_ok h.2.ctx⟩)
    have hb' := hb.mono (fun _ _ h => h) (fun x y ⟨_, a, c, h, hx, hy⟩ =>
      And.intro (hx.1.ctx h.1.ctx.ctx).r0 (hy.1.ctx h.2.ctx.ctx).r0)
    refine RelCT.seq (verifySetup_ct m b pk sig challenge) (RelCT.seq hb' ?_)
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, h3, hbytes⟩ ex ey
  have hb := byteMap_inj hbytes
  obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
  obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
  rw [← h0] at first
  rw [← h1] at middle
  rw [← h2] at last
  exact (hct s.mem (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, h1.symm, h2.symm, h3.symm, first.symm, middle.symm, last.symm⟩⟩ ex ey).1

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation :=
  verify_ct_of_body verifyBody_ct

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code verifyEquation
end VG.Impl.Ed25519.Arm
end

/-! The verification equation meets the reviewed contract and preserves the ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' :=
  verifyEquation_correct (VerifyPre.of hs)

private theorem returnFlag_value (v : BitVec 32) (b : Bool)
    (h : v.toNat = if b then 1 else 0) : v = if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> exact h

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans (returnFlag_value _ _ h)
  pub := by
    sig_implies_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifySatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifySatState

theorem verify_verified : Verified Arm.target verifyEquation (Spec.Ed25519.verifyEquationContract Arm.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.Arm
