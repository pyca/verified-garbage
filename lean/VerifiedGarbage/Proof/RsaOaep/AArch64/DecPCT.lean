module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecP
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecP
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on AArch64, given the key's precomputed values: verified

As for `vg_rsa_oaep_decrypt` (`Proof/RsaOaep/AArch64/DecVerified.lean`): two
calls whose public data agree, `pre`'s modulus' values among them, have the
same layout (`headP_ct`); the call of `vg_rsa_private_checked_precomputed`
leaks alike in both (`privP_ct`), `scratch` goes back to its slot
(`fixScr_ct`), and the rest is `vg_rsa_oaep_decrypt`'s (`after_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked stackArgs_fourteen)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)

/-- Ready for `vg_rsa_private_checked_precomputed`. -/
abbrev PrivReadyP : Inv := fun L g vv m₀ t =>
  Ctx L g vv m₀ t ∧ Ready L t ∧ PreX L m₀ ∧ ∃ V W, Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl) ∧
    Slots L W ∧ CallArgs L W

theorem headP_ok {ts : List FnTable} {P : Nat} {s : State} (h : (decSpecP ts P).pre s) (hP : 16 ≤ P) :
    WP isa (.block (decPrologue ++ privArgs ++ preArgs)) (entered s) (PrivReadyP (layP P s) s.gpr s.v s.mem) := by
  have hx := specP h
  have hL := hx.ok
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (prologueX_ok hL hx.rd hx.wr) fun t ⟨hc, h9, hpw⟩ => ?_
  rw [WP.block_append_iff, privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem (layP P s).Q (layP P s).scr (fun o => t.mem (off (layP P s).scr o))
      (fun j => word t.mem (layP P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots (layP P s) (privW (layP P s) fun j => word t.mem (layP P s).Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  refine WP.mono (privR_ok hL hP hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  refine WP.mono (preArgs_ok hL hP hx.pre hc2 hr2 (hm2 ▸ R1)) fun u3 ⟨hc3, hr3, R3⟩ => ?_
  exact ⟨hc3, hr3, hx.pre, _, _, R3, hS1, ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩⟩

/-- Two calls whose public data agree, in the inner frame. -/
def EnteredP (ts : List FnTable) (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpecP ts (S + 1)).pre s₁ ∧ (decSpecP ts (S + 1)).pre s₂ ∧ (decSpecP ts (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

theorem headP_ct (ts : List FnTable) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (EnteredP ts S) (.block (decPrologue ++ privArgs ++ preArgs)) (Two S ts PrivReadyP) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  have x₁ := specP h₁
  have x₂ := specP h₂
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, y₁, z₁⟩ := headP_ok h₁ (by omega_arith)
  obtain ⟨_, u₂, y₂, z₂⟩ := headP_ok h₂ (by omega_arith)
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  have e : layP (S + 1) s₂ = layP (S + 1) s₁ := by
    simp only [lay, dxP, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16, a17, a18, hsp]
  obtain ⟨hl₁, hl₂⟩ := List.append_inj hl (by simp only [List.length_map, List.length_append, bytesAt_length, h4, h6])
  obtain ⟨hn, he⟩ := leak_split hl₁ (by rw [bytesAt_length, bytesAt_length, h4])
  have hsy' : ∀ f ∈ Proof.HashTable.AArch64.tabFns ts, s₁.syms f = s₂.syms f :=
    fun f hf => hsy f (List.mem_append_left _ hf)
  have htaL : Proof.HashTable.AArch64.TabAgree ts (layP (S + 1) s₁).tabL s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨x₁.tabL, x₁.pw⟩, ⟨by rw [show (layP (S + 1) s₁).tabL = stackArg s₂ 15 from a15]; exact x₂.tabL, x₂.pw⟩, hsy',
      fun T hT => htabL _ _ rfl a15.symm T hT⟩
  have hta : Proof.HashTable.AArch64.TabAgree ts (layP (S + 1) s₁).tab s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨x₁.tab, x₁.pw⟩, ⟨by rw [show (layP (S + 1) s₁).tab = stackArg s₂ 16 from a16]; exact x₂.tab, x₂.pw⟩, hsy',
      fun T hT => htab _ _ rfl a16.symm T hT⟩
  refine ⟨ht, ⟨layP (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, x₁.ok, rfl,
    ⟨⟨?_, ?_, ?_⟩, htaL.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl),
      hta.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl)⟩, z₁, e ▸ z₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]
  · show Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 17) (s₁.gpr .x4).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₁ 17) (s₁.gpr .x4).toNat
    rw [hl₂, a17, h4]

/-! ## The call -/

theorem privP_args_eq {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {a : State}
    (ha : PrivReadyP L g vv m₀ a) (rd wr : List Region) :
    ∀ i < 14, stackArg (a.callEntry.withRegions rd wr) i =
      [L.p, L.pl, L.q, L.ql, L.dp, L.dpl, L.dq, L.dql, L.qi, L.qil, L.scr + BitVec.ofNat 64 8192,
        L.sl - BitVec.ofNat 64 1024, L.pre, L.prl].getD i 0 := by
  obtain ⟨hc, -, -, V, W, R, -, hA⟩ := ha
  intro i hi
  rw [stackArg_ce, hc.sp, show a.mem.readW (L.Q + BitVec.ofNat 64 (8 * i)) 64 = upd (upd W 12 L.pre) 13 L.prl i from
    R.fr i (by unfold nW frameBytes; omega_arith)]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  exacts [(upd2 (by decide)).trans hA.p, (upd2 (by decide)).trans (hA.args 0 (by decide)),
    (upd2 (by decide)).trans (hA.args 1 (by decide)), (upd2 (by decide)).trans (hA.args 2 (by decide)),
    (upd2 (by decide)).trans (hA.args 3 (by decide)), (upd2 (by decide)).trans (hA.args 4 (by decide)),
    (upd2 (by decide)).trans (hA.args 5 (by decide)), (upd2 (by decide)).trans (hA.args 6 (by decide)),
    (upd2 (by decide)).trans (hA.args 7 (by decide)), (upd2 (by decide)).trans (hA.args 8 (by decide)),
    (upd2 (by decide)).trans hA.s10, (upd2 (by decide)).trans hA.s11, by simp [upd], by simp [upd],
    absurd hi (by omega_arith)]

theorem privP_pub' {L : DLay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : PrivReadyP L g₁ v₁ m₁ a) (hb : PrivReadyP L g₂ v₂ m₂ b) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pub
      (a.callEntry.withRegions (privRdP L) (privWr L)) (b.callEntry.withRegions (privRdP L) (privWr L)) := by
  have aa := privP_args_eq ha (privRdP L) (privWr L)
  have ab := privP_args_eq hb (privRdP L) (privWr L)
  have hx := ha.2.2.1
  have hle : Spec.Rsa.precomputedWords L.k.toNat ≤ L.prl.toNat := by
    rw [hx.prlv]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  have e : ∀ i < 14, stackArg (a.callEntry.withRegions (privRdP L) (privWr L)) i =
      stackArg (b.callEntry.withRegions (privRdP L) (privWr L)) i := fun i hi => (aa i hi).trans (ab i hi).symm
  refine ⟨by rw [ha.1.sp, hb.1.sp], ?_, by rw [ha.2.1.x0, hb.2.1.x0], by rw [ha.2.1.x1, hb.2.1.x1],
    by rw [ha.2.1.x2, hb.2.1.x2], by rw [ha.2.1.x3, hb.2.1.x3], by rw [ha.2.1.x4, hb.2.1.x4],
    by rw [ha.2.1.x5, hb.2.1.x5], by rw [ha.2.1.x6, hb.2.1.x6], by rw [ha.2.1.x7, hb.2.1.x7],
    e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
    e 12 (by decide), e 13 (by decide)⟩
  have hl := hk.2.2
  rw [hx.lk] at hl
  simp only [Spec.Rsa.privatePrecomputedLeak] at hl ⊢
  rw [ha.2.1.x2, ha.2.1.x3, ha.2.1.x4, ha.2.1.x5, hb.2.1.x2, hb.2.1.x3, hb.2.1.x4, hb.2.1.x5,
    aa 12 (by decide), ab 12 (by decide)]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L), ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L),
    hk.1, hk.2.1, hx.words hL ha.1 hle, hb.2.2.1.words hL hb.1 hle, hl]

/-- After the call: the frame's words with `pre` and `pre_len` in words 12
and 13. -/
abbrev CalledP : Inv := fun L g vv m₀ t => ∃ W, Called L g vv m₀ (upd (upd W 12 L.pre) 13 L.prl) t ∧ Slots L W

theorem privP_ct (c : PrivPChecked) {S : Nat} (hS : c.stack = S + 1) (ts : List FnTable) :
    RelCT isa (Two S ts PrivReadyP) (.call c.name c.code) (Two S ts CalledP) := by
  have hv : Verified AArch64.target c.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)) :=
    hS ▸ c.verified
  exact two_wp (fun e => RelCT.call (n := c.name) hv.1 hv.2.1 (privRdP e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ => by
      obtain ⟨c₁, r₁, x₁, V₁, W₁, R₁, s₁, A₁⟩ := f₁
      obtain ⟨c₂, r₂, x₂, V₂, W₂, R₂, s₂, A₂⟩ := f₂
      exact ⟨privP_pre hL hP x₁ c₁ r₁ R₁ A₁, privP_pre hL hP x₂ c₂ r₂ R₂ A₂,
        privP_pub' hL hk.1 ⟨c₁, r₁, x₁, V₁, W₁, R₁, s₁, A₁⟩ ⟨c₂, r₂, x₂, V₂, W₂, R₂, s₂, A₂⟩,
        (covers_privP hL x₁ c₁).1, (covers_privP hL x₁ c₁).2, (covers_privP hL x₂ c₂).1,
        (covers_privP hL x₂ c₂).2⟩)
    fun _ _ _ _ _ hL hP ⟨hc, hr, hx, V, W, R, hSl, hA⟩ =>
      WP.mono (privP_call c hL (hP.trans hS.symm) hx hc hr R hA) fun _ h => ⟨W, h, hSl⟩

/-! ## `scratch` back to its slot -/

theorem fixScr_ct {S : Nat} (hS : 15 ≤ S) (ts : List FnTable) :
    RelCT isa (Two S ts CalledP) (.block fixScr) (Two S ts CalledI) :=
  two [] (by taint_decide)
    (fun _ _ _ _ _ _ _ _ _ _ ⟨_, f₁, _⟩ ⟨_, f₂, _⟩ =>
      ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL hP ⟨_, hcl, hSl⟩ => WP.mono (fixScr_ok hL (by omega_using [hS, hP]) hcl) fun _ h => ⟨_, h, slots_fix hSl⟩

/-! ## The whole function -/

theorem pubP_sp {ts : List FnTable} {P : Nat} {s₁ s₂ : State} (h : (decSpecP ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at h
  exact h.1

variable {vs : List MdHash} (hc : Coh vs)

include hc in
theorem decP_ct (c : PrivPChecked) {S : Nat} (hS : c.stack = S + 1) (h15 : 15 ≤ S) :
    ConstantTime isa (decSpecP (tables vs) (S + 1)).pre (decSpecP (tables vs) (S + 1)).pub
      (decryptP (fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pubP_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBodyP_eq]
  refine ((headP_ct (tables vs) h15).seq ((privP_ct c hS (tables vs)).seq ((fixScr_ct h15 (tables vs)).seq
    (after_ct hc h15)))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

include hc in
/-- `vg_rsa_oaep_decrypt_precomputed`, calling `c`, for the tables of `vs`. -/
theorem decP_verified (c : PrivPChecked) (h16 : 16 ≤ c.stack)
    (hsat : ∃ s, (decSpecP (tables vs) c.stack).pre s) :
    Verified AArch64.target (decryptP (fnsOf vs) c.name c.code) (decSpecP (tables vs) c.stack) := by
  obtain ⟨S, hS⟩ : ∃ S, c.stack = S + 1 := ⟨c.stack - 1, by omega_using [h16]⟩
  have hct := decP_ct hc c hS (by omega)
  rw [← hS] at hct
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := decP_ok hc c h16 h
    exact ⟨t, s', he, hp⟩) hct (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec
