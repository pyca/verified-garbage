module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public meta import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.VectorCrypto
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
public import VerifiedGarbage.TCB.AArch64.Residue
meta import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Key
meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.VectorCrypto
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.TCB.AArch64.Residue

/-!
# SM4 key expansion with the Armv8 SM4 instructions meets its contract

`keyInit_ok`: the key, its words made big-endian and XORed with `FK` from
the table, is `MK ⊕ FK` (`Proof.Sm4.keyInit`), a word to a lane.
`keyGroup_ok`: `sm4ekey` with four words of `CK` from the table is a `quad`
of the key schedule's rounds (`sm4EKey_eq`), stored to the schedule.
`keyGroups_ok`: the eight groups in turn, with what is stored so far; the
sixteen bytes at `16 r` are the state after `r + 1` groups, whose word
`i mod 4` is the round key `rk_i` (`Proof.Sm4.rkOf`, `expandKey_eq`).
`expandKey_verified`: `vg_sm4_expand_key_sm4` meets
`Spec.Sm4.expandKeyContract` with no stack, and is constant time by the
taint analysis with the pointers public.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Sm4e

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Sm4e
open VG.Spec.Sm4 (Word Block blockAt scheduleAt ck fk)
open VG.Proof.Sm4 (quad quads ofBlock rkOf)
open VG.Proof.Aes.AArch64.Aese (setV_v_self setV_v_of_ne exec_ldrq exec_strq)
open VG.Proof.Sm4.AArch64.Serial (keyContract keyTaint_agree keySat)

/-- Words `4 i … 4 i + 3` of the constants, a word to a lane. -/
def kQuad (i : Nat) : BitVec 128 :=
  ofVWords (keyWord (4 * i)) (keyWord (4 * i + 1)) (keyWord (4 * i + 2)) (keyWord (4 * i + 3))

/-- The constants as `ldrqTbl` reads them from the table. -/
theorem keyTable_quad : ∀ n < 9, keyTable.getD (16 * n / 8 + 1) 0 ++ keyTable.getD (16 * n / 8) 0 = kQuad n := by
  decide

theorem keyTable_length : keyTable.length = 18 := by simp [keyTable]

/-- The first four words are `FK`. -/
theorem kQuad_fk : kQuad 0 = ofVWords (fk.getD 0 0) (fk.getD 1 0) (fk.getD 2 0) (fk.getD 3 0) := rfl

/-- The others are `CK`. -/
theorem kQuad_ck (m : Nat) :
    kQuad (m + 1) = ofVWords (ck (4 * m)) (ck (4 * m + 1)) (ck (4 * m + 2)) (ck (4 * m + 3)) := by
  simp only [kQuad, keyWord, ite_eq_right (show ¬ 4 * (m + 1) < 4 by omega_using []),
    ite_eq_right (show ¬ 4 * (m + 1) + 1 < 4 by omega_using []),
    ite_eq_right (show ¬ 4 * (m + 1) + 2 < 4 by omega_using []),
    ite_eq_right (show ¬ 4 * (m + 1) + 3 < 4 by omega_using []),
    show 4 * (m + 1) - 4 = 4 * m by omega_using [], show 4 * (m + 1) + 1 - 4 = 4 * m + 1 by omega_using [],
    show 4 * (m + 1) + 2 - 4 = 4 * m + 2 by omega_using [], show 4 * (m + 1) + 3 - 4 = 4 * m + 3 by omega_using []]

/-- Loading words `4 j … 4 j + 3` of the constants from the table at `x9`. -/
theorem exec_kld {j : Nat} (hj : j < 9) {s : State} (hx : s.gpr .x9 = s.syms keyName) :
    exec (kld j) s = some (s.setV .v1 (kQuad j)) := by
  have hc : s.gpr .x9 = s.syms keyName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧ 16 * j / 8 + 2 ≤ keyTable.length :=
    ⟨hx, by omega_arith, by omega_arith, by rw [keyTable_length]; omega_arith⟩
  simp only [kld, exec, ite_eq_left_of_eq_true _ _ (eq_true hc), keyTable_quad j hj]

theorem vword_xor (x y : BitVec 128) (e : Nat) : vword (x ^^^ y) e = vword x e ^^^ vword y e :=
  BitVec.extractLsb'_xor ..

/-- The key's words XOR `FK`'s. -/
theorem init_eq (m : Mem) (p : Addr) :
    VRevOp.rev32b.eval (m.readW p 128) ^^^ kQuad 0 = vec (Proof.Sm4.keyInit (blockAt m p)) := by
  rw [rev32b_readW, kQuad_fk]
  refine vec_ext fun e he => ?_
  rw [vword_xor, vec, vec, vword_ofVWords _ _ _ _ he, vword_ofVWords _ _ _ _ he, vword_ofVWords _ _ _ _ he,
    four_getElem _ he, four_getElem (fun w => fk.getD w 0) he, four_getElem _ he]
  rfl

theorem exec_rev32 (s : State) :
    exec (.vop (.rev .rev32b .v0 .v0)) s = some (s.setV .v0 (VRevOp.rev32b.eval (s.v .v0))) := by
  simp only [exec, reduceVOpEval, Option.map_some]

theorem exec_eor (s : State) :
    exec (.vop (.logic .eor .v0 .v0 .v1)) s = some (s.setV .v0 (s.v .v0 ^^^ s.v .v1)) := by
  simp only [exec, reduceVOpEval, Option.map_some]

theorem exec_ekey (s : State) :
    exec (.vop (.sm4ekey .v0 .v0 .v1)) s = some (s.setV .v0 (sm4EKey (s.v .v0) (s.v .v1))) := by
  simp only [exec, reduceVOpEval, Option.map_some]

theorem keyStart_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 16) :
    ∃ t, runBlock isa keyStart s = some t ∧
      t.v .v0 = vec (Proof.Sm4.keyInit (blockAt s.mem (s.gpr .x0))) ∧ t.gpr .x9 = t.syms keyName ∧
      (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e₁ : exec (.ldrq .v0 .x0 0) s = some (s.setV .v0 (s.mem.readW (s.gpr .x0) 128)) := by
    have := exec_ldrq (s := s) (t := .v0) (n := .x0) (off := 0) (by decide) (by rw [BitVec.add_zero]; exact hr)
    rwa [BitVec.add_zero] at this
  rw [keyStart, runBlock_cons, e₁, runStep_some, runBlock_cons, exec_rev32, runStep_some, runBlock_cons,
    exec_adrSym, runStep_some, runBlock_cons, exec_kld (by decide) (gpr_write_self _ _ _ _),
    runStep_some, runBlock_cons, exec_eor, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [v_setV, v_write, reduceCtorEq, ↓reduceIte]
    exact init_eq _ _
  · simp only [gpr_setV, gpr_write, ↓reduceIte]
    rfl
  · simp only [gpr_setV, gpr_write, hr, ↓reduceIte]
  · simp only [mem_setV, mem_write]
  · simp only [rd_setV, rd_write]
  · simp only [wr_setV, wr_write]
  · simp only [sp_setV, sp_write]

/-- A group of four rounds from the state `x`: its round keys, the next
state, stored at `16 i` in the schedule. -/
theorem keyGroup_ok {s : State} {i : Nat} (hi : i < 8) (hx : s.gpr .x9 = s.syms keyName)
    (hw : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * i)) 16) {x : Nat → Word} (hv : s.v .v0 = vec x) :
    ∃ t, runBlock isa (keyGroup i) s = some t ∧ t.v .v0 = vec (quad .key ck i x) ∧
      t.gpr = s.gpr ∧ t.syms = s.syms ∧
      t.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (16 * i)) 16 (vec (quad .key ck i x)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have ev : sm4EKey ((s.setV .v1 (kQuad (i + 1))).v .v0) ((s.setV .v1 (kQuad (i + 1))).v .v1) =
      vec (quad .key ck i x) := by
    rw [v_setV_of_ne _ _ (by decide), v_setV_self, hv, kQuad_ck, sm4EKey_eq]
  rw [keyGroup, runBlock_cons, exec_kld (by omega_using [hi]) hx, runStep_some, runBlock_cons, exec_ekey, ev,
    runStep_some, runBlock_cons,
    exec_strq (by omega_using [hi]) (by simp only [wr_setV, gpr_setV]; exact hw), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [v_setV_self]
  · simp only [gpr_setV]
  · dsimp only
    rw [v_setV_self, mem_setV, mem_setV, gpr_setV, gpr_setV]
  · simp only [rd_setV]
  · simp only [wr_setV]
  · simp only [sp_setV]

/-- The first `n` groups: the state after them, and the states stored. -/
theorem keyGroups_ok (x : Nat → Word) (s₀ : State) (hw : (⟨s₀.gpr .x1, 128⟩ : Region) ∈ s₀.wr) :
    ∀ n ≤ 8, ∀ s : State, s.gpr .x9 = s.syms keyName → s.gpr .x1 = s₀.gpr .x1 → s.wr = s₀.wr → s.v .v0 = vec x →
    ∃ t, runBlock isa ((List.range n).flatMap keyGroup) s = some t ∧ t.v .v0 = vec (quads .key ck n x) ∧
      t.gpr = s.gpr ∧ t.syms = s.syms ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      ∀ r < n, t.mem.readW (s₀.gpr .x1 + BitVec.ofNat 64 (16 * r)) 128 = vec (quads .key ck (r + 1) x)
  | 0, _, s, _, _, _, hv => ⟨s, rfl, hv, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_using [])⟩
  | n + 1, hn, s, hx, h1, hwr, hv => by
    obtain ⟨a, ae, av, ag, asy, ard, awr, asp, am⟩ := keyGroups_ok x s₀ hw n (by omega_using [hn]) s hx h1 hwr hv
    obtain ⟨b, be, bv, bg, bsy, bm, brd, bwr, bsp⟩ := keyGroup_ok (s := a) (i := n) (by omega_using [hn])
      (by rw [ag, hx, asy])
      (by
        rw [awr, hwr, ag, h1]
        exact ⟨_, hw, Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn])⟩) av
    refine ⟨b, ?_, bv, bg.trans ag, bsy.trans asy, brd.trans ard, bwr.trans awr, bsp.trans asp, fun r hr => ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · rw [bm, ag, h1]
      by_cases h : r = n
      · subst h
        show ((Mem.write _ _ 16 _).read _ 16).setWidth 128 = _
        rw [Proof.VectorCrypto.read_write16]
        rfl
      · show ((Mem.write _ _ 16 _).read _ 16).setWidth 128 = _
        rw [Mem.read_write_sep (Offset.sep (s₀.gpr .x1) (by omega_using [h, hr]) (by omega_using [hn, hr])
          (by omega_using [hn])) (by decide)]
        exact am r (by omega_using [hr, h])

/-! ## The function -/

theorem expandKey_wp {s : State} (hp : keyContract.pre s) : WP isa expandKeyBody s (keyContract.post s) := by
  obtain ⟨hrd, hwr⟩ := hp
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 16 :=
    ⟨⟨s.gpr .x0, 16⟩, by rw [hrd]; simp, Region.contains_self _ _⟩
  obtain ⟨a, ae, av, a9, ag, am, ard, awr, asp⟩ := keyStart_ok hr
  obtain ⟨b, be, bv, bg, bsy, brd, bwr, bsp, bm⟩ := keyGroups_ok (Proof.Sm4.keyInit (blockAt s.mem (s.gpr .x0))) s
    (by rw [hwr]; simp) 8 (Nat.le_refl _) a a9 (ag _ (by decide)) awr av
  refine WP.of_runBlock ⟨b, ?_, ?_⟩
  · rw [VG.Interleave.runBlock_append, ae, Option.bind_some, be]
  · show scheduleAt b.mem (s.gpr .x1) = Spec.Sm4.expandKey (blockAt s.mem (s.gpr .x0))
    rw [Proof.Sm4.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    have e : (scheduleAt b.mem (s.gpr .x1))[i] = (scheduleAt b.mem (s.gpr .x1)).getD i 0 := by
      simp [Vector.getD, hi]
    have hm : i % 4 < 4 := Nat.mod_lt _ (by decide)
    have h2 := vword_readW b.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * (i / 4))) hm
    rw [Offset.add_add_eq (s.gpr .x1) (show 16 * (i / 4) + 4 * (i % 4) = 4 * i by omega_using []),
      bm (i / 4) (by omega_using [hi]), vec, vword_ofVWords _ _ _ _ hm, four_getElem _ hm] at h2
    rw [e, schedule_getD _ _ hi, ← h2]
    rfl

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKeyBody s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved) (expandKey_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem expandKey_ct : ConstantTime isa keyContract.pre keyContract.pub expandKeyBody :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) keyTaint_agree (by taint_decide)

/-- The key schedule meets the contract, with no stack. -/
theorem expandKeyBody_verified :
    Verified AArch64.target expandKeyBody (Spec.Sm4.expandKeyContract AArch64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, keyContract, AArch64.abi,
      AArch64.argRegs] [keySat] using keySat)

/-- `vg_sm4_expand_key_sm4` meets its contract, with no stack. -/
theorem expandKey_verified : Verified AArch64.target expandKey (Spec.Sm4.expandKeyContract AArch64.abi) :=
  Clears.Verified.withClears expandKeyBody_verified (by decide)

/-- `vg_sm4_expand_key_sm4` returns without secret residue
(`RTaint.noResidue_of_check`). -/
theorem expandKey_noResidue (k : Contract isa) : NoResidue expandKey k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-! ## ECB, returning without secret residue

`vg_sm4_ecb_encrypt_sm4` and `vg_sm4_ecb_decrypt_sm4` leave the blocks in
`v0`–`v7` and the round keys in `v16`–`v23`, and clear them before they
return. -/

/-- The vector registers `ecb` leaves secrets in. -/
def ecbLeft : List VReg := Impl.Sm4.AArch64.Fn.ecbLeft

/-- `ecb dir`, then `ecbLeft` cleared. -/
abbrev ecbCleared (dir : VG.Impl.Sm4.AArch64.Dir) : Prog isa := Impl.Sm4.AArch64.Fn.ecb dir

theorem ecbCleared_verified (dir : VG.Impl.Sm4.AArch64.Dir) :
    Verified AArch64.target (ecbCleared dir) (Spec.Sm4.ecbContract AArch64.abi (dirOf dir)) :=
  Clears.Verified.withClears (ecb_verified dir) (by decide)

theorem ecbCleared_noResidue (k : Contract isa) : ∀ dir, NoResidue (ecbCleared dir) k 0
  | .encrypt => RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k
  | .decrypt => RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.Sm4e.expandKey_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Sm4.AArch64.Sm4e.expandKey
      (Spec.Sm4.expandKeyContract AArch64.abi) 0 :=
  ⟨Proof.Sm4.AArch64.Sm4e.expandKey_verified,
    Proof.Sm4.AArch64.Sm4e.expandKey_noResidue _⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.Sm4e.ecbEncrypt_scrubbed :
    VerifiedScrubbed AArch64.target (Impl.Sm4.AArch64.Fn.ecb Impl.Sm4.AArch64.Dir.encrypt)
      (Spec.Sm4.ecbContract AArch64.abi (Proof.Sm4.AArch64.Sm4e.dirOf Impl.Sm4.AArch64.Dir.encrypt)) 0 :=
  ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .encrypt,
    Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .encrypt⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Sm4.AArch64.Sm4e.ecbDecrypt_scrubbed :
    VerifiedScrubbed AArch64.target (Impl.Sm4.AArch64.Fn.ecb Impl.Sm4.AArch64.Dir.decrypt)
      (Spec.Sm4.ecbContract AArch64.abi (Proof.Sm4.AArch64.Sm4e.dirOf Impl.Sm4.AArch64.Dir.decrypt)) 0 :=
  ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .decrypt,
    Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .decrypt⟩

end VG.Proof.Sm4.AArch64.Sm4e
