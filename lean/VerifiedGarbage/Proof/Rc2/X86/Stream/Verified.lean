import VerifiedGarbage.Proof.Rc2.X86.Stream.InitCorrect
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateLong

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): everything before the call

The state before the call of the CBC function (`Mid`): the copies done, and
its arguments in `eax`, `ecx`, `edx`, `esi` and `ebx` (`head_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `shr d, n`, and ZF. -/
theorem wp_shrZ {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.zf = some (s.gpr d >>> n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

theorem shr3 (x : BitVec 32) : x >>> 3 = BitVec.ofNat 32 (x.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The state before the call, from the entry state `s₀`. -/
structure Mid (s₀ s : State) : Prop where
  common : Common s₀ s
  ebx : s.gpr .ebx = scr s₀
  eax : s.gpr .eax = ctx s₀
  ecx : s.gpr .ecx = ctx s₀ + 128
  edx : s.gpr .edx = op s₀
  esi : s.gpr .esi = BitVec.ofNat 32 (O s₀ / 8)
  zf : s.zf = some (decide (O s₀ = 0))
  short : O s₀ = 0 →
    Spec.Rc2.bytesAt s.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
      Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀)
  out : O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (oA s₀) (O s₀) =
      Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀)
  pend : O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
      Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8)

theorem cbcArgs_ok {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .ebx = scr s₀ → t.gpr .eax = ctx s₀ →
      t.gpr .ecx = ctx s₀ + 128 → t.gpr .edx = op s₀ → t.gpr .esi = BitVec.ofNat 32 (O s₀ / 8) →
      t.zf = some (decide (O s₀ = 0)) → Q t) :
    WP isa (.block cbcArgs) s Q := by
  have hOe := hp.O_eq
  refine wp_arg hp hc (i := 6) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_mov fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_addi fun s₄ u₄ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 4) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_arg hp c₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine wp_shrZ ⟨by decide, by decide⟩ fun s₇ u₇ hz₇ => WP.block_nil ?_
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (O s₀ / 8) := by rw [u₇.gpr, u₆.gpr, shr3]
  refine hQ s₇ (c₆.upd u₇ (by decide) (by decide) (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]) esi₇ ?_
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  rw [hz₇, ← u₇.gpr, esi₇, ofNat_beq_zero (by omega)]
  exact congrArg some (decide_eq_decide.mpr (by omega))

theorem head_ok {s₀ : State} (hp : Pre s₀) : WP isa head s₀ (Mid s₀) := by
  refine WP.seq (entry_ok hp fun s c f hz => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => Common s₀ t ∧
      (O s₀ = 0 → Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀)) ∧
      (O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (oA s₀) (O s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀)) ∧
      (O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8)))
    (WP.ite _ hz (fun h => ?_) (fun h => ?_)) fun t ⟨ct, h₁, h₂, h₃⟩ => cbcArgs_ok hp ct
      fun u cu mu ebx eax ecx edx esi zf =>
        ⟨cu, ebx, eax, ecx, edx, esi, zf, fun h => mu ▸ h₁ h, fun h => mu ▸ h₂ h, fun h => mu ▸ h₃ h⟩)
  · have h0 : O s₀ = 0 := by simpa using h
    exact short_ok hp h0 c f fun s' c' b => ⟨c', fun _ => b, fun h => absurd h0 h, fun h => absurd h0 h⟩
  · have h0 : O s₀ ≠ 0 := by simpa using h
    exact long_ok hp h0 c f fun s' c' b₁ b₂ => ⟨c', fun h => absurd h h0, fun _ => b₁, fun _ => b₂⟩

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the call of the CBC function

The call of the verified CBC function on the blocks at `out` (`cbcCall_ok`),
from the state before it (`Mid`), in a frame of its arguments.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

/-- The registers pushed as the callee's arguments. -/
abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem cbcCall_eq (d : Spec.Rc2.Direction) :
    cbcCall d = .frame (.push rs5) (.call (cbcName d) (Impl.Rc2.X86.Cbc.cbc d)) (.pop .eax 5) := by
  cases d <;> rfl

theorem cbc_nosp (d : Spec.Rc2.Direction) : NoSp (Impl.Rc2.X86.Cbc.cbc d) := by
  apply NoSp.of_all
  cases d
  · change Impl.Rc2.X86.Cbc.encrypt.allInstrs _ = true
    lit_decide
  · change Impl.Rc2.X86.Cbc.decrypt.allInstrs _ = true
    lit_decide

theorem cbc_stack (d : Spec.Rc2.Direction) : stackUse (Impl.Rc2.X86.Cbc.cbc d) = 16 := by
  cases d <;> rfl

/-- The regions the CBC function reads (beyond those it writes), and writes. -/
def callRd (s₀ s : State) : List Region :=
  [⟨(ctx s₀).setWidth 64, 128⟩, ⟨argAddr (pushed rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region :=
  [⟨(ctx s₀ + 128).setWidth 64, 8⟩, ⟨oA s₀, 8 * (O s₀ / 8)⟩, ⟨sA s₀, 512⟩]

theorem iv_eq {s₀ : State} (hp : Pre s₀) : (ctx s₀ + 128).setWidth 64 = cA s₀ + BitVec.ofNat 64 128 :=
  addr_eq (x := ctx s₀) (k := 128) (by have := hp.c_fit; omega)

section
variable {s₀ s : State} (hp : Pre s₀) (hm : Mid s₀ s)
include hp hm

theorem callEntry_args :
    arg (pushed rs5 s).callEntry 0 = ctx s₀ ∧ arg (pushed rs5 s).callEntry 1 = ctx s₀ + 128 ∧
      arg (pushed rs5 s).callEntry 2 = op s₀ ∧
      arg (pushed rs5 s).callEntry 3 = BitVec.ofNat 32 (O s₀ / 8) ∧
      arg (pushed rs5 s).callEntry 4 = scr s₀ := by
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hm.common.esp]; have := hp.sp_lo; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit hrs (by simp)]
  · exact hm.eax
  · exact hm.ecx
  · exact hm.edx
  · exact hm.esi
  · exact hm.ebx

omit hp in
theorem callEntry_sp : (pushed rs5 s).callEntry.gpr .esp = E s₀ - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hm.common.esp]; rfl

omit hp in
theorem callEntry_argAddr : argAddr (pushed rs5 s).callEntry 0 = (E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
  rw [callEntry_argAddr0, hm.common.esp]; rfl

theorem callPre_ok (d : Spec.Rc2.Direction) :
    VG.X86.CallPre (Cbc.contract d) rs5 (callRd s₀ s) (callWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp hm
  have eSp := callEntry_sp hm
  have eA := callEntry_argAddr hm
  have hOe := hp.O_eq
  have hlo := hp.sp_lo
  have hcf := hp.c_fit
  have hof := hp.o_fit
  have hEf := hp.sp_fit
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have e8 : 8 * (O s₀ / 8) = O s₀ := by omega
  have ivE := iv_eq hp
  have hesp : s.gpr .esp = E s₀ := hm.common.esp
  -- The stack the frame and the callee use.
  have kA : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (stkR s₀) := by
    have := below_inner (sp := E s₀) (a := 4) (b := 40) (k := 20) (by omega) hlo
    rw [show E s₀ - BitVec.ofNat 32 24 = E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have kS : Region.Sub (below (E s₀ - BitVec.ofNat 32 24) 16) (stkR s₀) := below_inner (by omega) hlo
  have ivS : Region.Sub ⟨(ctx s₀ + 128).setWidth 64, 8⟩ (ctxR s₀) := by rw [ivE]; exact Pre.iv_sub
  have oS : Region.Sub ⟨oA s₀, 8 * (O s₀ / 8)⟩ (oR s₀) := by rw [e8]; exact fun _ h => h
  have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cbc.contract, callRd, callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, by rw [toNat_ofNat_lt (by omega)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [ivE]; exact Pre.sch_iv
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left Pre.sch_sub).sub_right oS
    · exact (hp.c_s.sub_left Pre.sch_sub).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left ivS).sub_right oS
    · exact (hp.c_s.sub_left ivS).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.o_s.sub_left oS).sub_right bS
    · exact (hp.k_c.sub_left kA).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kA).sub_right oS
    · exact (hp.k_s.sub_left kA).sub_right bS
    · exact (hp.k_c.sub_left kR).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kR).sub_right oS
    · exact (hp.k_s.sub_left kR).sub_right bS
    · exact (hp.k_c.sub_left kS).sub_right Pre.sch_sub
    · exact (hp.k_c.sub_left kS).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kS).sub_right oS
    · exact (hp.k_s.sub_left kS).sub_right bS
    · omega
    · show (ctx s₀ + BitVec.ofNat 32 128).toNat + 8 ≤ _
      rw [toNat_add_ofNat (by omega)]; omega
    · have := hp.s_fit; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [toNat_ofNat_lt (by omega)]; omega
  · have wr : s.wr = [ctxR s₀, oR s₀, scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [callRd, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · have wr : s.wr = [ctxR s₀, oR s₀, scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of the CBC function on the `O / 8` blocks at `out`: it writes only the
chaining value, `out`, its scratch space and the stack below `esp`. -/
theorem cbcCall_ok (d : Spec.Rc2.Direction) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [ivR s₀, oR s₀, ⟨sA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      Spec.Rc2.blocksAt s'.mem (oA s₀) (O s₀ / 8) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (cA s₀)) d
        (Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8))).1 →
      Spec.Rc2.blockAt s'.mem (cA s₀ + BitVec.ofNat 64 128) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (cA s₀)) d
          (Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8))).2 →
      Q s') :
    WP isa (cbcCall d) s Q := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp hm
  have hlo := hp.sp_lo
  have hOe := hp.O_eq
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have e8 : 8 * (O s₀ / 8) = O s₀ := by omega
  have ivE := iv_eq hp
  have hesp : s.gpr .esp = E s₀ := hm.common.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (stkR s₀) := by
    rw [hesp]; exact below_sub (by decide) hlo
  have oS : Region.Sub ⟨oA s₀, 8 * (O s₀ / 8)⟩ (oR s₀) := by rw [e8]; exact fun _ h => h
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  rw [cbcCall_eq]
  refine WP.callWith (k := Cbc.contract d) (fun s h => Cbc.cbc_body_correct d s h) (cbc_nosp d) (by simp)
    hrs (by rw [cbc_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (callPre_ok hp hm d) fun s' rd wr cs f ⟨s₂, m₂, post⟩ => ?_
  have ce := callEntry_frame fit hrs
  simp only [Cbc.contract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32,
    toNat_ofNat_lt (show O s₀ / 8 < 2 ^ 32 by omega), ivE] at post
  have sch : Spec.Rc2.scheduleAt (pushed rs5 s).callEntry.mem (cA s₀) = Spec.Rc2.scheduleAt s.mem (cA s₀) :=
    Proof.Rc2.scheduleAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.sch_sub).symm)
  have iv : Spec.Rc2.blockAt (pushed rs5 s).callEntry.mem (cA s₀ + BitVec.ofNat 64 128) =
      Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128) :=
    Proof.Rc2.blockAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.iv_sub).symm)
  have out : Spec.Rc2.blocksAt (pushed rs5 s).callEntry.mem (oA s₀) (O s₀ / 8) =
      Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8) :=
    Proof.Rc2.blocksAt_frame ce _ _ (sing ((hp.k_o.sub_left kE).sub_right oS).symm)
  rw [sch, iv, out] at post
  refine hQ s' rd wr cs (f.sub fun r hr => ?_) post.1 post.2
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨ivR s₀, by simp, by rw [ivE]; exact fun _ h => h⟩
  · exact ⟨oR s₀, by simp, oS⟩
  · exact ⟨⟨sA s₀, 512⟩, by simp, fun _ h => h⟩
  · refine ⟨stkR s₀, by simp, ?_⟩
    rw [cbc_stack, hesp]; exact fun _ h => h

end

/-- Our caller's `esi` and `ebx`, from the scratch space at `ebx`. -/
theorem restore_ok {s₀ s : State} (hp : Pre s₀) (hebx : s.gpr .ebx = scr s₀)
    (hwr : s.wr = s₀.wr) (h₁ : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx)
    (h₂ : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, t.mem = s.mem → t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi →
      (∀ r, r ≠ .ebx → r ≠ .esi → t.gpr r = s.gpr r) → Q t) :
    WP isa (.block restore) s Q := by
  have rin {d : Nat} (hd : d + 4 ≤ 576) : InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
    obtain ⟨r, hr, hc⟩ := hp.sin hwr hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [restore]
  refine wp_ldm (o := 516) hebx (rin (d := 516) (by decide)) fun s₁ u₁ => ?_
  refine wp_ldm (o := 512) (B := scr s₀) (by rw [u₁.other _ (by decide)]; exact hebx)
    (by rw [u₁.rd, u₁.wr]; exact rin (d := 512) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine hQ s₂ (by rw [u₂.mem, u₁.mem]) (by rw [u₂.gpr, u₁.mem]; exact h₁)
    (by rw [u₂.other _ (by decide), u₁.gpr]; exact h₂) fun r a b => ?_
  rw [u₂.other _ a, u₁.other _ b]

end VG.Proof.Rc2.X86.Stream.Update

end

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions are correct

From the state before the call (`Mid`): with no complete block, the data is
already appended to the pending bytes; otherwise the CBC function runs on
`out`. Then our caller's registers are restored, and `update_post_short` or
`update_post_long` gives the contract's postcondition.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem update_correct (d : Spec.Rc2.Direction) (s₀ : State) (hs : (updateContract d).pre s₀) :
    WP isa (update d) s₀ (fun s' => abiPreserved s₀ s' ∧ (updateContract d).post s₀ s') := by
  have hp := pre_of hs
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hlo := hp.sp_lo
  have hOe' : (arg s₀ 5).toNat = (p s₀ + len s₀) / 8 * 8 := hp.O_eq
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  have retStk : (retR s₀).Disjoint (stkR s₀) := by
    show Region.Disjoint ⟨(E s₀).setWidth 64, 4⟩ ⟨(E s₀ - BitVec.ofNat 32 40).setWidth 64, 40⟩
    rw [Taint.sub_setWidth hlo]; exact Offset.base_disjoint_below _ (by decide)
  -- What `Common` keeps.
  have sep3 {r : Region} (h₁ : r.Disjoint (pendR s₀)) (h₂ : r.Disjoint (oR s₀)) (h₃ : r.Disjoint (scR s₀)) :
      ∀ x ∈ [pendR s₀, oR s₀, scR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    exacts [h₁, h₂, h₃]
  have schC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (schR s₀).Disjoint x :=
    sep3 Pre.sch_pend (hp.c_o.sub_left Pre.sch_sub) (hp.c_s.sub_left Pre.sch_sub)
  have ivC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (ivR s₀).Disjoint x :=
    sep3 Pre.iv_pend (hp.c_o.sub_left Pre.iv_sub) (hp.c_s.sub_left Pre.iv_sub)
  have retC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (retR s₀).Disjoint x :=
    sep3 (hp.sep_pend _ (by simp)) hp.r_o hp.r_s
  -- What the call keeps.
  have sep4 {r : Region} (h₁ : r.Disjoint (ivR s₀)) (h₂ : r.Disjoint (oR s₀))
      (h₃ : r.Disjoint ⟨sA s₀, 512⟩) (h₄ : r.Disjoint (stkR s₀)) :
      ∀ x ∈ [ivR s₀, oR s₀, ⟨sA s₀, 512⟩, stkR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    exacts [h₁, h₂, h₃, h₄]
  have buf : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  rw [update]
  refine WP.seq (WP.mono (head_ok hp) fun s hm => ?_)
  have hc := hm.common
  refine WP.seq (WP.ite _ hm.zf (fun h => WP.block_nil ?_) (fun h => ?_))
  · -- No complete block.
    have h0 : O s₀ = 0 := by simpa using h
    refine restore_ok hp hm.ebx hc.wr hc.ebx hc.esi fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide)]; exact hc.edi
      · rw [to _ (by decide) (by decide)]; exact hc.ebp
      · rw [to _ (by decide) (by decide)]; exact hc.esp
    · rw [mt]; exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have post := update_post_short (m := s₀.mem) (m' := t.mem) (ctx := cA s₀) (data := dA s₀)
        (out := oA s₀) (d := d) (p := p s₀) (len := len s₀) (by omega)
        (by rw [mt]; exact Proof.Rc2.scheduleAt_frame hc.frame _ schC)
        (by rw [mt]; exact Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by rw [mt]; exact hm.short h0)
      simp only [updateContract]
      rw [hOe']
      exact post
  · -- The CBC function on `out`.
    have h0 : O s₀ ≠ 0 := by simpa using h
    refine cbcCall_ok hp hm d fun s' rd wr cs f c₁ c₂ => ?_
    have word {e : Nat} (he : 512 ≤ e) (he' : e + 4 ≤ 576) :
        s'.mem.readW (addr (scr s₀) e) 32 = s.mem.readW (addr (scr s₀) e) 32 := by
      refine f.readW (Region.contains_self _ _) (sep4 ?_ ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left Pre.iv_sub).symm.sub_left (hp.scr_sub he')
      · exact hp.o_s.symm.sub_left (hp.scr_sub he')
      · rw [hp.scr_addr he']; exact Offset.disjoint_base _ he (by omega)
      · exact hp.k_s.symm.sub_left (hp.scr_sub he')
    refine restore_ok hp (by rw [cs .ebx (by simp [calleeSaved])]; exact hm.ebx) (wr.trans hc.wr)
      (by rw [word (by decide) (by decide)]; exact hc.ebx) (by rw [word (by decide) (by decide)]; exact hc.esi)
      fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.edi
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.ebp
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.esp
    · rw [mt, f.readW (Region.contains_self _ _) (sep4 (hp.r_c.sub_right Pre.iv_sub) hp.r_o
        (hp.r_s.sub_right buf) retStk) (by decide)]
      exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have e8 : (p s₀ + len s₀) / 8 * 8 / 8 = (p s₀ + len s₀) / 8 := Nat.mul_div_cancel _ (by decide)
      have pendS : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, (p s₀ + len s₀) % 8⟩ (pendR s₀) :=
        Region.sub_prefix (by have := Nat.mod_lt (p s₀ + len s₀) (by decide : 0 < 8); omega)
      have out := hm.out h0
      have pend := hm.pend h0
      rw [hOe] at out pend c₁ c₂
      rw [e8] at c₁ c₂
      have post := update_post_long (m := s₀.mem) (m₁ := s.mem) (m' := t.mem) (ctx := cA s₀) (data := dA s₀)
        (out := oA s₀) (d := d) (p := p s₀) (len := len s₀) hpl (by omega) out
        (Proof.Rc2.scheduleAt_frame hc.frame _ schC) (Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by
          show Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) _ = _
          rw [mt, Proof.Rc2.bytesAt_frame f _ _ (by omega) (sep4
            ((Pre.iv_pend).symm.sub_left pendS) ((hp.c_o.sub_left Pre.pend_sub).sub_left pendS)
            (((hp.c_s.sub_left Pre.pend_sub).sub_left pendS).sub_right buf)
            ((hp.k_c.sub_right Pre.pend_sub).symm.sub_left pendS))]
          exact pend)
        (by
          rw [mt]
          exact Proof.Rc2.scheduleAt_frame f _ (sep4 Pre.sch_iv (hp.c_o.sub_left Pre.sch_sub)
            ((hp.c_s.sub_left Pre.sch_sub).sub_right buf) (hp.k_c.sub_right Pre.sch_sub).symm))
        (by rw [mt]; exact c₁) (by rw [mt]; exact c₂)
      simp only [updateContract]
      rw [hOe']
      exact post

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): constant time

The taint analysis proves everything but the call of the CBC function (which
restores registers the analysis then takes for secret), from the public
arguments on the stack (`τ0`); the call is related in both runs by
`RelCT.callWith`, from what the correctness proof knows of the state it is
made from (`Mid`), and the restore of our caller's registers through `ebx`,
public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- The arguments on the stack are public, and only read. -/
def τ0 : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 32 }

theorem τ0_wf {s : State} (f : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r) :
    VG.X86.Taint.Wf τ0 s :=
  Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨f, fun r hr => Taint.frame_disjoint (n := 28) (by omega) (d r hr).1 (d r hr).2⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem τ0_agree {s₁ s₂ : State} (f₁ : (s₁.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨(s₁.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₁ 0, 28⟩ r)
    (d₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨(s₂.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₂ 0, 28⟩ r)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 7, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree τ0 s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τ0_wf f₁ d₁, τ0_wf f₂ d₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => sp,
    fun k h4 hk => ?_⟩
  · simp only [τ0, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [τ0] at hk
    rw [show Taint.depth τ0.stk = 0 from rfl, Nat.zero_add, Taint.argByte_eq f₁ h4 hk,
      Taint.argByte_eq f₂ h4 hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

namespace Update

open VG.Impl.Rc2.X86.Stream

def Rel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (updateContract d).pre s₁ ∧ (updateContract d).pre s₂ ∧ (updateContract d).pub s₁ s₂

theorem Pre.disj {s : State} (hp : Pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_o, hp.a_o⟩, ⟨hp.r_s, hp.a_s⟩]

theorem rel_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : Rel d s₁ s₂) :
    VG.X86.Taint.Agree τ0 s₁ s₂ :=
  τ0_agree (pre_of h.1).sp_fit (pre_of h.2.1).sp_fit (pre_of h.1).disj (pre_of h.2.1).disj h.2.2.1 h.2.2.2

/-- After `head`, in both runs. -/
def MidRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Rel d σ₁ σ₂ ∧ Mid σ₁ s₁ ∧ Mid σ₂ s₂

theorem call_ct (d : Spec.Rc2.Direction) :
    RelCT isa (fun s₁ s₂ => MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  have ct : RelCT isa (fun s₁ s₂ => MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun _ _ => True) := by
    rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, m₁, m₂⟩, -⟩ e₁ e₂
    have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp₁ m₁
    obtain ⟨b0, b1, b2, b3, b4⟩ := callEntry_args hp₂ m₂
    have rd : callRd σ₂ s₂ = callRd σ₁ s₁ := by
      simp only [callRd, callEntry_argAddr m₁, callEntry_argAddr m₂, ctx, E, sp, args 0 (by decide)]
    have wr : callWr σ₂ = callWr σ₁ := by
      simp only [callWr, ctx, oA, O, sA, op, scr, args 0 (by decide), args 4 (by decide), args 5 (by decide),
        args 6 (by decide)]
    have ct' : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (cbcCall d) (fun _ _ => True) := by
      rw [cbcCall_eq]
      apply RelCT.callWith (fun s h => Cbc.cbc_body_correct d s h) (Cbc.cbc_constantTime d) (callRd σ₁ s₁)
        (callWr σ₁)
      rintro a b ⟨rfl, rfl⟩
      refine ⟨callPre_ok hp₁ m₁ d, by rw [← rd, ← wr]; exact callPre_ok hp₂ m₂ d, ?_, ?_, ?_⟩
      · rw [m₁.common.esp, m₂.common.esp]; exact sp
      · simp only [State.withRegions_gpr, callEntry_sp m₁, callEntry_sp m₂, E, sp]
      · intro i hi
        simp only [arg_withRegions]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
        · rw [a0, b0, ctx, ctx, args 0 (by decide)]
        · rw [a1, b1, ctx, ctx, args 0 (by decide)]
        · rw [a2, b2, op, op, args 4 (by decide)]
        · rw [a3, b3, O, O, args 5 (by decide)]
        · rw [a4, b4, scr, scr, args 6 (by decide)]
    exact ct' _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  refine (ct.wpDep (F := fun (σ s' : State) => s'.gpr .ebx = σ.gpr .ebx) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, ⟨h₁, h₂, -⟩, m₁, m₂⟩, -⟩ := h
    exact ⟨cbcCall_ok (pre_of h₁) m₁ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved]),
      cbcCall_ok (pre_of h₂) m₂ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved])⟩
  · rintro s₁' s₂' ⟨-, s₁, s₂, ⟨⟨σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩, e₁, e₂⟩
    rw [e₁, e₂, m₁.ebx, m₂.ebx, scr, scr, args 6 (by decide)]

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold update
  have hA : RelCT isa (Rel d) head (fun _ _ => True) :=
    RelCT.taint (A := taint) τ0 (fun _ _ h => rel_agree h) (by taint_decide)
  refine (hA.wpDep (F := Mid) fun s₁ s₂ (h : Rel d s₁ s₂) => ⟨head_ok (pre_of h.1), head_ok (pre_of h.2.1)⟩).seq
    (RelCT.seq (R := fun (s₁ s₂ : State) => s₁.gpr .ebx = s₂.gpr .ebx) ?_ ?_)
  · apply RelCT.ite
    · rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩
      show s₁.zf = s₂.zf
      rw [m₁.zf, m₂.zf, O, O, args 5 (by decide)]
    · apply RelCT.nil
      rintro s₁ s₂ ⟨⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩
      rw [m₁.ebx, m₂.ebx, scr, scr, args 6 (by decide)]
    · exact (call_ct d).mono (fun _ _ h => ⟨h.1.2, h.2⟩) (fun _ _ h => h)
  · exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end Update

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the shared contracts

The shared contracts (`Spec.Rc2.cbcInitContract`,
`Spec.Rc2.cbcUpdateContract`) let the code write its arguments; `wideInit` and
`wideUpdate` are the per-target contracts with that permission, which imply
the shared ones. `narrow*` drop it again, for the proofs against
`initContract` and `updateContract`.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- `initContract`, with the arguments writable. -/
def wideInit : Contract isa :=
  { initContract with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
      let iv : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let ctx : Region := ⟨(arg s 5).setWidth 64, 144⟩
      let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 24
      s.rd = [key, iv] ∧ s.wr = [ctx, buf, args] ∧
        key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
        stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
        (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
        (arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

/-- `updateContract d`, with the arguments writable. -/
def wideUpdate (d : Spec.Rc2.Direction) : Contract isa :=
  { updateContract d with
    pre := fun s =>
      let ctx : Region := ⟨(arg s 0).setWidth 64, 144⟩
      let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let out : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
      let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 40
      s.rd = [data] ∧ s.wr = [ctx, out, buf, args] ∧
        ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ data.Disjoint out ∧
        data.Disjoint buf ∧ out.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint out ∧ args.Disjoint buf ∧
        ret.Disjoint ctx ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧
        stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧
        (arg s 0).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
        (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
        (arg s 1).toNat < 8 ∧ (arg s 5).toNat = ((arg s 1).toNat + (arg s 3).toNat) / 8 * 8 }

/-- `init(0x1000, 1, 8, 0x2000, 8, 0x3000, 0x4000)`. -/
def initSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 1 else if a = 0x600c then 8 else
    if a = 0x6011 then 0x20 else if a = 0x6014 then 8 else if a = 0x6019 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

/-- `update(0x1000, 0, 0x2000, 0, 0x3000, 0, 0x4000)`. -/
def updateSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x600d then 0x20 else if a = 0x6015 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

syntax "wide_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wide_pre [$ls,*]) => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›)))

theorem init_implies : wideInit.Implies (Spec.Rc2.cbcInitContract abi 24) where
  pre := by
    wide_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  post := by
    sig_implies_post [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  pub := by
    sig_implies_pub [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below]
  sat := by
    sig_implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argSlots, argVal, argBytes,
      wideInit, initContract, below] [initSat, arg, argAddr, Mem.readW, Mem.read] using initSat

theorem update_implies (d : Spec.Rc2.Direction) :
    (wideUpdate d).Implies (Spec.Rc2.cbcUpdateContract abi d 40) where
  pre := by
    wide_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  post := by
    sig_implies_post [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  pub := by
    sig_implies_pub [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below]
  sat := by
    sig_implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argSlots, argVal, argBytes,
      wideUpdate, updateContract, below] [updateSat, arg, argAddr, Mem.readW, Mem.read] using updateSat

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is constant time

As for the updates (`UpdateCT.lean`): the taint analysis proves the checks and
the copy of the IV, `RelCT.callWith` the call of the key expansion, and the
restore of our caller's registers through `ebx`, public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def Rel (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

theorem Pre.disj {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  have e : argAddr s 0 = argAddr s₀ 0 := by unfold argAddr; rw [hc.esp]
  rw [hc.wr, hp.wr, hc.esp, e]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_s, hp.a_s⟩]

/-- The arguments, from a state whose memory is the entry state's. -/
theorem arg_eq {s₀ s : State} (hc : Common s₀ s) (hm : s.mem = s₀.mem) (i : Nat) : arg s i = arg s₀ i := by
  unfold arg argAddr; rw [hc.esp, hm]

theorem agree_mid {σ₁ σ₂ s₁ s₂ : State} (h : Rel σ₁ σ₂) (c₁ : Common σ₁ s₁) (c₂ : Common σ₂ s₂)
    (m₁ : s₁.mem = σ₁.mem) (m₂ : s₂.mem = σ₂.mem) : VG.X86.Taint.Agree τ0 s₁ s₂ := by
  have hp₁ := pre_of h.1
  have hp₂ := pre_of h.2.1
  refine τ0_agree (by rw [c₁.esp]; exact hp₁.sp_fit) (by rw [c₂.esp]; exact hp₂.sp_fit) (hp₁.disj c₁)
    (hp₂.disj c₂) (by rw [c₁.esp, c₂.esp]; exact h.2.2.1) fun i hi => ?_
  rw [arg_eq c₁ m₁, arg_eq c₂ m₂]; exact h.2.2.2 i hi

theorem code_eq {σ₁ σ₂ : State} (args : ∀ i < 7, arg σ₁ i = arg σ₂ i) : code σ₁ = code σ₂ := by
  simp only [code, kl, eb, il, args 1 (by decide), args 2 (by decide), args 4 (by decide)]

/-- After the checks and the test of their result. -/
structure Checked (s₀ s : State) : Prop where
  common : Common s₀ s
  mem : s.mem = s₀.mem
  zf : s.zf = some (decide (code s₀ = 0))
  ebx : s.gpr .ebx = s₀.gpr .ebx
  esi : s.gpr .esi = s₀.gpr .esi

theorem checked_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq checks (.block [.alu .test .eax (.reg .eax)])) s₀ (Checked s₀) := by
  refine WP.seq (checks_ok hp fun s c m a b e => wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  refine ⟨c.fupd f₁, by rw [f₁.mem, m], ?_, by rw [f₁.gpr]; exact b, by rw [f₁.gpr]; exact e⟩
  rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := code_lt s₀; omega)]

/-- Before the call. -/
structure Args (s₀ s : State) : Prop where
  common : Common s₀ s
  eax : s.gpr .eax = key s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = arg s₀ 2
  esi : s.gpr .esi = ctx s₀
  ebx : s.gpr .ebx = scr s₀

def CheckedRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ Checked σ₁ s₁ ∧ Checked σ₂ s₂

def ArgsRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ code σ₁ = 0 ∧ Args σ₁ s₁ ∧ Args σ₂ s₂

theorem args_ct :
    RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs) ArgsRel := by
  have ct : RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs)
      (fun _ _ => True) := by
    refine RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, -⟩ := h
    exact agree_mid hσ k₁.common k₂.common k₁.mem k₂.mem
  have code0 : ∀ {σ s : State}, Checked σ s → isa.eval .ne s = some false → code σ = 0 := fun k z => by
    have : isa.eval .ne _ = _ := congrArg (Option.map (!·)) k.zf
    rw [z] at this
    exact of_decide_eq_true (by revert this; cases decide (code _ = 0) <;> simp)
  have h : ∀ σ : State × State, RelCT isa (fun s₁ s₂ =>
      (CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) ∧ Rel σ.1 σ.2 ∧ Checked σ.1 s₁ ∧ Checked σ.2 s₂ ∧
        code σ.1 = 0) (.block initArgs) ArgsRel := fun σ => by
    refine ((ct.mono (fun _ _ h => h.1) (fun _ _ h => h)).wp
      (F₁ := fun (s : State) => Rel σ.1 σ.2 ∧ code σ.1 = 0 ∧ Args σ.1 s) (F₂ := Args σ.2) fun s₁ s₂ h => ?_).mono
      (fun _ _ h => h) fun _ _ h => ⟨σ.1, σ.2, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩
    obtain ⟨-, hσ, k₁, k₂, h0⟩ := h
    have hp₁ := pre_of hσ.1
    have hp₂ := pre_of hσ.2.1
    have h0' : code σ.2 = 0 := (code_eq hσ.2.2.2).symm.trans h0
    exact ⟨initArgs_ok hp₁ (code_ok h0).2.2 k₁.common k₁.mem k₁.ebx k₁.esi
        fun t c ea ec ed es eb _ _ _ => ⟨hσ, h0, c, ea, ec, ed, es, eb⟩,
      initArgs_ok hp₂ (code_ok h0').2.2 k₂.common k₂.mem k₂.ebx k₂.esi
        fun t c ea ec ed es eb _ _ _ => ⟨c, ea, ec, ed, es, eb⟩⟩
  refine (RelCT.exists_ h).mono (fun s₁ s₂ hh => ?_) (fun _ _ h => h)
  obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩ := hh
  exact ⟨(σ₁, σ₂), ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩, hσ, k₁, k₂, code0 k₁ z⟩

theorem call_ct : RelCT isa ArgsRel keyCall (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, h0, a₁, a₂⟩ e₁ e₂
  have hp₁ := pre_of h₁
  have hp₂ := pre_of h₂
  have h0' : code σ₂ = 0 := (code_eq args).symm.trans h0
  obtain ⟨hk₁, he₁, -⟩ := code_ok h0
  obtain ⟨hk₂, he₂, -⟩ := code_ok h0'
  have pre₁ := keyCallPre_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
  have pre₂ := keyCallPre_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
  have fit (s : State) (σ : State) (hp : Pre σ) (c : Common σ s) : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [c.esp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have esp : s₁.gpr .esp = s₂.gpr .esp := by rw [a₁.common.esp, a₂.common.esp]; exact sp
  have rd : callRd σ₂ s₂ = callRd σ₁ s₁ := by
    simp only [callRd, callEntry_argAddr0, esp, keyR, kA, kl, key, args 0 (by decide), args 1 (by decide)]
  have wr : callWr σ₂ = callWr σ₁ := by
    simp only [callWr, schR, cA, sA, ctx, scr, args 5 (by decide), args 6 (by decide)]
  have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) keyCall (fun _ _ => True) := by
    apply RelCT.callWith key_body_correct expandKey_constantTime (callRd σ₁ s₁) (callWr σ₁)
    intro a b hab
    rw [hab.1, hab.2]
    refine ⟨pre₁, by rw [← rd, ← wr]; exact pre₂, esp, ?_, ?_⟩
    · simp only [State.withRegions_gpr, callEntry_esp', esp]
    · intro i hi
      simp only [arg_withRegions]
      rw [callEntry_arg (fit _ _ hp₁ a₁.common) hrs (by simpa using hi),
        callEntry_arg (fit _ _ hp₂ a₂.common) hrs (by simpa using hi)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .eax = s₂.gpr .eax; rw [a₁.eax, a₂.eax, key, key, args 0 (by decide)]
      · show s₁.gpr .ecx = s₂.gpr .ecx; rw [a₁.ecx, a₂.ecx, args 1 (by decide)]
      · show s₁.gpr .edx = s₂.gpr .edx; rw [a₁.edx, a₂.edx, args 2 (by decide)]
      · show s₁.gpr .esi = s₂.gpr .esi; rw [a₁.esi, a₂.esi, ctx, ctx, args 5 (by decide)]
      · show s₁.gpr .ebx = s₂.gpr .ebx; rw [a₁.ebx, a₂.ebx, scr, scr, args 6 (by decide)]
  obtain ⟨ht, -, b₁, b₂⟩ := (ct.wp (F₁ := fun (s : State) => s.gpr .ebx = scr σ₁) (F₂ := fun (s : State) => s.gpr .ebx = scr σ₂)
    fun a b ⟨ha, hb⟩ => by
      subst ha hb
      exact ⟨keyCall_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₁.ebx,
        keyCall_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₂.ebx⟩) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, show u₁.gpr .ebx = u₂.gpr .ebx by rw [b₁, b₂, scr, scr, args 6 (by decide)]⟩

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold init
  apply RelCT.assoc
  have hA : RelCT isa Rel (.seq checks (.block [.alu .test .eax (.reg .eax)])) (fun _ _ => True) :=
    RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => agree_mid h (Common.refl _) (Common.refl _) rfl rfl)
      (by taint_decide)
  refine ((hA.wpDep (F := Checked) fun s₁ s₂ (h : Rel s₁ s₂) =>
    ⟨checked_ok (pre_of h.1), checked_ok (pre_of h.2.1)⟩).mono (fun _ _ h => h)
      (Q' := CheckedRel) fun _ _ h => h.2).seq ?_
  apply RelCT.ite
  · rintro s₁ s₂ ⟨σ₁, σ₂, ⟨-, -, -, args⟩, k₁, k₂⟩
    show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [k₁.zf, k₂.zf, code_eq args]
  · exact RelCT.nil fun _ _ _ => trivial
  · unfold initBody
    refine args_ct.seq (call_ct.seq ?_)
    exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end VG.Proof.Rc2.X86.Stream.Init

end

/-!
# Streaming RC2-CBC on x86 (32-bit): `Verified`

`init` and the updates meet `initContract` and `updateContract`, with their
arguments only read; the shared contracts let the code write them too
(`wideInit`, `wideUpdate`), which `Verified.narrowTo` allows, and
`init_implies` and `update_implies` take the proofs to the shared contracts.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-! ## `init` -/

def initRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 28⟩]
def initWr (s : State) : List Region := [⟨(arg s 5).setWidth 64, 144⟩, ⟨(arg s 6).setWidth 64, 576⟩]

def updateRd (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 28⟩]
def updateWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 144⟩, ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩, ⟨(arg s 6).setWidth 64, 576⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Stream.initContract, VG.Proof.Rc2.X86.Stream.wideInit,
    VG.Proof.Rc2.X86.Stream.updateContract, VG.Proof.Rc2.X86.Stream.wideUpdate,
    VG.Proof.Rc2.X86.Stream.initRd, VG.Proof.Rc2.X86.Stream.initWr,
    VG.Proof.Rc2.X86.Stream.updateRd, VG.Proof.Rc2.X86.Stream.updateWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit_pre (s : State) (h : wideInit.pre s) : initContract.pre (s.withRegions (initRd s) (initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem wideUpdate_pre (d : Spec.Rc2.Direction) (s : State) (h : (wideUpdate d).pre s) :
    (updateContract d).pre (s.withRegions (updateRd s) (updateWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target Impl.Rc2.X86.Stream.init (Spec.Rc2.cbcInitContract abi 24) := by
  have hsat := init_implies.sat_left
  have narrowSat : ∃ s, initContract.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Init.init_correct s hs) Init.init_constantTime (.refl narrowSat))
    initRd initWr wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem update_verified (d : Spec.Rc2.Direction) :
    Verified target (Impl.Rc2.X86.Stream.update d) (Spec.Rc2.cbcUpdateContract abi d 40) := by
  have hsat := (update_implies d).sat_left
  have narrowSat : ∃ s, (updateContract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideUpdate_pre d s hs⟩
  apply Verified.of_implies _ (update_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Update.update_correct d s hs) (Update.update_constantTime d)
      (.refl narrowSat))
    updateRd updateWr (wideUpdate_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [updateRd, updateWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.encryptUpdate (Spec.Rc2.cbcEncryptUpdateContract abi 40) :=
  update_verified .encrypt

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.decryptUpdate (Spec.Rc2.cbcDecryptUpdateContract abi 40) :=
  update_verified .decrypt

end VG.Proof.Rc2.X86.Stream
