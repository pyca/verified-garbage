module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCTBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecPriv
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCTBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecPriv
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-OAEP decryption on AArch64: constant time, to the decoding

The prologue and the private-key operation's arguments (`head_ct`), from two
entry states whose public data agree; the private-key operation
(`priv_ct`); the address of the table of the label's hash function to its
slot (`tabSlot_ct`) and its digest length to `x16` (`lenLoad_ct`), which
both runs take as that of the same table (`WithL`), so that they take the
same branch on it (`byLen_ct`); the private-key operation's result to its
slot and the check of `k` (`resK_ct`); and the failure for a short `k`
(`decFail_tr`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl privK)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.AArch64 (tables tableOf Coh tabOK_of held_tableOf)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)

/-! ## The prologue and the arguments -/

/-- Ready for the private-key operation. -/
abbrev PrivReady : Inv := fun L g vv m₀ t =>
  Ctx L g vv m₀ t ∧ Ready L t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Slots L W ∧ CallArgs L W

theorem head_ok {ts : List FnTable} {P : Nat} {s : State} (h : (decSpec ts P).pre s)
    (hP : 16 ≤ P) :
    WP isa (.block (decPrologue ++ privArgs)) (entered s) (PrivReady (lay P s) s.gpr s.v s.mem) := by
  have hL := lay_ok h
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok h) fun t ⟨hc, h9, hpw⟩ => ?_
  rw [privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem (lay P s).Q (lay P s).scr (fun o => t.mem (off (lay P s).scr o))
      (fun j => word t.mem (lay P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots (lay P s) (privW (lay P s) fun j => word t.mem (lay P s).Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  refine WP.mono (privR_ok hL hP hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  refine ⟨hc2, hr2, _, _, hm2 ▸ R1, hS1, ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩⟩

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (ts : List FnTable) (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpec ts (S + 1)).pre s₁ ∧ (decSpec ts (S + 1)).pre s₂ ∧ (decSpec ts (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

theorem head_ct (ts : List FnTable) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Entered ts S) (.block (decPrologue ++ privArgs)) (Two S ts PrivReady) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hL₁, hT₁, hd₁⟩ := spec_tab h₁
  obtain ⟨hL₂, hT₂, hd₂⟩ := spec_tab h₂
  sig_pub [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := head_ok h₁ (by omega_arith)
  obtain ⟨_, u₂, x₂, y₂⟩ := head_ok h₂ (by omega_arith)
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay (S + 1) s₂ = lay (S + 1) s₁ := by
    simp only [lay, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16, hsp]
  obtain ⟨hn, he⟩ := leak_split hl (by rw [bytesAt_length, bytesAt_length, h4])
  have hsy' : ∀ f ∈ Proof.HashTable.AArch64.tabFns ts, s₁.syms f = s₂.syms f :=
    fun f hf => hsy f (List.mem_append_left _ hf)
  have htaL : Proof.HashTable.AArch64.TabAgree ts (lay (S + 1) s₁).tabL s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨hL₁, hd₁⟩, ⟨by rw [show (lay (S + 1) s₁).tabL = stackArg s₂ 15 from a15]; exact hL₂, hd₂⟩, hsy',
      fun T hT => htabL _ _ rfl a15.symm T hT⟩
  have hta : Proof.HashTable.AArch64.TabAgree ts (lay (S + 1) s₁).tab s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨hT₁, hd₁⟩, ⟨by rw [show (lay (S + 1) s₁).tab = stackArg s₂ 16 from a16]; exact hT₂, hd₂⟩, hsy',
      fun T hT => htab _ _ rfl a16.symm T hT⟩
  refine ⟨ht, ⟨lay (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, lay_ok h₁, rfl,
    ⟨⟨?_, ?_⟩, htaL.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl),
      hta.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl)⟩, y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]

/-! ## The private-key operation -/

theorem priv_args_eq {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {a : State}
    (ha : PrivReady L g vv m₀ a) (rd wr : List Region) :
    ∀ i < 12, stackArg (a.callEntry.withRegions rd wr) i =
      [L.p, L.pl, L.q, L.ql, L.dp, L.dpl, L.dq, L.dql, L.qi, L.qil, L.scr + BitVec.ofNat 64 8192,
        L.sl - BitVec.ofNat 64 1024].getD i 0 := by
  obtain ⟨hc, -, V, W, R, -, hA⟩ := ha
  intro i hi
  rw [stackArg_ce, hc.sp, show a.mem.readW (L.Q + BitVec.ofNat 64 (8 * i)) 64 = W i from
    R.fr i (by unfold nW frameBytes; omega_arith)]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  exacts [hA.p, hA.args 0 (by decide), hA.args 1 (by decide), hA.args 2 (by decide), hA.args 3 (by decide),
    hA.args 4 (by decide), hA.args 5 (by decide), hA.args 6 (by decide), hA.args 7 (by decide),
    hA.args 8 (by decide), hA.s10, hA.s11, absurd hi (by omega_arith)]

theorem priv_pub' {L : DLay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : PrivReady L g₁ v₁ m₁ a) (hb : PrivReady L g₂ v₂ m₂ b) :
    (privK S).pub (a.callEntry.withRegions (privRd L) (privWr L))
      (b.callEntry.withRegions (privRd L) (privWr L)) := by
  have aa := priv_args_eq ha (privRd L) (privWr L)
  have ab := priv_args_eq hb (privRd L) (privWr L)
  simp only [privK, State.withRegions_sp, State.callEntry_sp, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.2.1.x0, ha.2.1.x1, ha.2.1.x2, ha.2.1.x3, ha.2.1.x4, ha.2.1.x5, ha.2.1.x6, ha.2.1.x7, hb.2.1.x0, hb.2.1.x1,
    hb.2.1.x2, hb.2.1.x3, hb.2.1.x4, hb.2.1.x5, hb.2.1.x6, hb.2.1.x7, ha.1.sp, hb.1.sp, true_and]
  refine ⟨fun i hi => (aa i hi).trans (ab i hi).symm, ?_, ?_⟩
  · rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L)]; exact hk.1
  · rw [ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L)]; exact hk.2

/-- After the call. -/
abbrev CalledI : Inv := fun L g vv m₀ t => ∃ W, Called L g vv m₀ W t ∧ Slots L W

theorem priv_ct (v : PrivImpl) (ts : List FnTable) :
    RelCT isa (Two v.S ts PrivReady) (.call v.name v.code) (Two v.S ts CalledI) :=
  two_wp (fun e => RelCT.call (n := v.name) v.correct v.ct (privRd e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ => by
      obtain ⟨c₁, r₁, V₁, W₁, R₁, s₁, A₁⟩ := f₁
      obtain ⟨c₂, r₂, V₂, W₂, R₂, s₂, A₂⟩ := f₂
      exact ⟨priv_pre' hL hP c₁ r₁ R₁ A₁, priv_pre' hL hP c₂ r₂ R₂ A₂,
        priv_pub' hL hk.1 ⟨c₁, r₁, V₁, W₁, R₁, s₁, A₁⟩ ⟨c₂, r₂, V₂, W₂, R₂, s₂, A₂⟩,
        (covers_priv hL c₁).1, (covers_priv hL c₁).2, (covers_priv hL c₂).1, (covers_priv hL c₂).2⟩)
    fun _ _ _ _ _ hL hP ⟨hc, hr, V, W, R, hS, hA⟩ => WP.mono (priv_call v hL hP hc hr R hA) fun _ h => ⟨W, h, hS⟩

/-! ## The table of the label's hash function -/

/-- After the private-key operation, with the address of the table of the
label's hash function in its slot. -/
abbrev SlotI : Inv := fun L g vv m₀ t => In L g vv m₀ (fun W _ => W 32 = L.tabL) t

/-- And its digest length `D` in `x16`. -/
abbrev LenI (D : Nat) : Inv := fun L g vv m₀ t =>
  In L g vv m₀ (fun W t => W 32 = L.tabL ∧ t.gpr .x16 = BitVec.ofNat 64 D) t

section
variable {vs : List MdHash} (hc : Coh vs) {w₁ : MdHash} (hw₁ : w₁ ∈ vs)

include hc hw₁ in
theorem tabSlot_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S (tables vs) (WithL (tables vs) (tableOf w₁) CalledI)) (.block (tabSlot 15))
      (Two S (tables vs) (WithL (tables vs) (tableOf w₁) SlotI)) :=
  two [] (by taint_decide)
    (fun _ _ _ _ _ _ _ _ _ _ ⟨⟨_, f₁, _⟩, _⟩ ⟨⟨_, f₂, _⟩, _⟩ =>
      ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun L g vv m₀ t hL hP h => by
      obtain ⟨⟨W, hcl, hSl⟩, hh, hd⟩ := h
      have hP16 : 16 ≤ L.P := by omega_arith
      obtain ⟨hmL, -, hDL⟩ := held_tableOf hh
      have TL := hcl.ctx.tabL hL hP16 (tabOK_of hc hd hw₁) hmL hDL
      exact WP.mono (Table.wp_sy (tabSlot_ok (by decide) (hcl.ctx.lay hL hP16 hcl.rep hSl.scr) hcl.rep TL))
        fun u ⟨⟨_, Su, Ru, _⟩, sy⟩ => WithL.of (Φ := CalledI) (Ψ := SlotI) ⟨⟨W, hcl, hSl⟩, hh, hd⟩ sy
          (In.of_step hL hP16 hcl.ctx Su nil_ws Ru (hSl.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)])
            (X := fun W _ => W 32 = L.tabL) (by simp [upd]))

include hc hw₁ in
theorem lenLoad_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S (tables vs) (WithL (tables vs) (tableOf w₁) SlotI)) (.block lenLoad)
      (Two S (tables vs) (WithL (tables vs) (tableOf w₁) (LenI w₁.H.D))) := by
  refine two_wp (fun e => ?_) fun L g vv m₀ t hL hP h => ?_
  · show RelCT isa _ (.block ([.ldrSp .x16 sTab] ++ [.ldr .x .x16 .x16 32])) _
    refine (RelCT.block_append (pw_seq_tr (X := fun W _ => W 32 = e.L.tabL) [.x16] (fun _ => e.L.tabL)
      (by taint_decide) (by taint_decide) fun g vv m₀ t V W hL hP hc R hS h32 => ?_)).mono
      (fun _ _ ⟨hL, hP, _, f₁, f₂⟩ => ⟨hL, hP, f₁.1, f₂.1⟩) fun _ _ h => h
    have Ly := hc.lay hL (by omega_arith) R hS.scr
    have h256 : InRegions (t.rd ++ t.wr) (e.L.Q + BitVec.ofNat 64 256) 8 := Ly.ld (d := 256) (by decide)
    have r32 := R.rd8 (d := 256) (k := 32) rfl (by decide) h32
    oaep_run [sTab, h256, Ly.sp, r32]
    and_intros <;> first | trivial | rfl | (intro r hr; rw [List.mem_singleton.mp hr]; rfl)
  · obtain ⟨⟨hcx, V, W, R, hSl, h32⟩, hh, hd⟩ := h
    have hP16 : 16 ≤ L.P := by omega_arith
    obtain ⟨hmL, -, hDL⟩ := held_tableOf hh
    have TL := hcx.tabL hL hP16 (tabOK_of hc hd hw₁) hmL hDL
    exact WP.mono (Table.wp_sy (lenLoad_ok (hcx.lay hL hP16 R hSl.scr) R h32 TL.rdD (TL.mem _ (Frame.refl _ _)).2.1))
      fun u ⟨⟨Su, hm, h16, _⟩, sy⟩ => WithL.of (Φ := SlotI) (Ψ := LenI w₁.H.D) ⟨⟨hcx, V, W, R, hSl, h32⟩, hh, hd⟩ sy
        (In.of_step hL hP16 hcx Su nil_ws (hm ▸ R) hSl (X := fun W t => W 32 = L.tabL ∧
          t.gpr .x16 = BitVec.ofNat 64 w₁.H.D) ⟨h32, h16⟩)

end

/-- `byLen` in two runs with the same digest length `D` in `x16`: both take
the branch of `D`. -/
theorem byLen_ct {S : Nat} {ts : List FnTable} {b : Nat → Prog isa} {Q : State → State → Prop} {Φ : Inv} {D : Nat}
    (hΦ : ∀ L g vv m₀ t, Φ L g vv m₀ t → Ctx L g vv m₀ t) (hD : D < 4096)
    (h16 : ∀ L g vv m₀ t, Φ L g vv m₀ t → t.gpr .x16 = BitVec.ofNat 64 D)
    (hst : ∀ L g vv m₀ (t u : State), L.Ok → L.P = S + 1 → Φ L g vv m₀ t → Step L.Q L.scr [] t u →
      u.mem = t.mem → u.syms = t.syms → (∀ r, r ≠ .x17 → u.gpr r = t.gpr r) → Φ L g vv m₀ u)
    (hb : RelCT isa (Two S ts Φ) (b D) Q) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 4096) → RelCT isa (Two S ts Φ) (byLen b ds) Q
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    have hx0 := hx x (List.mem_cons_self ..)
    have hev : ∀ u : State, (u.gpr .x17 == 0) = decide (D = x) →
        isa.eval (.zero .x .x17) u = some (decide (D = x)) := fun u hz => by
      show eval (.zero .x .x17) u = _
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]
    have hback : ∀ s₁ s₂ (c : Option Bool), (Two S ts (fun L g vv m₀ t => Φ L g vv m₀ t ∧
        (t.gpr .x17 == 0) = decide (D = x)) s₁ s₂ ∧ isa.eval (.zero .x .x17) s₁ = c) → Two S ts Φ s₁ s₂ :=
      fun _ _ _ ⟨⟨e, hL, hP, hk, ⟨fa, _⟩, ⟨fb, _⟩⟩, _⟩ => ⟨e, hL, hP, hk, fa, fb⟩
    refine RelCT.seq (two (Ψ := fun L g vv m₀ t => Φ L g vv m₀ t ∧ (t.gpr .x17 == 0) = decide (D = x)) []
      (check_of_zImm (τ := Taint.ofRegs []) (c := .block [.subImm .x .x17 .x16 x])
        (c' := .block [.subImm .x .x17 .x16 0]) rfl (by taint_decide))
      (fun _ _ _ _ _ _ _ _ _ _ fa fb => ⟨(hΦ _ _ _ _ _ fa).sp.trans (hΦ _ _ _ _ _ fb).sp.symm,
        fun _ h => absurd h List.not_mem_nil⟩)
      fun L g vv m₀ t hL hP hφ => WP.mono (Table.wp_sy (cmpLen_ok (F := L.Q) (S := L.scr) (h16 _ _ _ _ _ hφ) hD hx0))
        fun u ⟨⟨hz, st, hm, hg⟩, sy⟩ => ⟨hst _ _ _ _ _ _ hL hP hφ st hm sy hg, hz⟩) ?_
    refine RelCT.ite (fun a b ⟨_, _, _, _, ⟨_, za⟩, ⟨_, zb⟩⟩ => by rw [hev a za, hev b zb]) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun a b h => hback a b _ h) fun _ _ h => h
      · exact RelCT.of_false fun a _ ⟨⟨_, _, _, _, ⟨_, za⟩, _⟩, ht⟩ => by rw [hev a za] at ht; simp [hDx] at ht
    · by_cases hDx : D = x
      · exact RelCT.of_false fun a _ ⟨⟨_, _, _, _, ⟨_, za⟩, _⟩, ht⟩ => by rw [hev a za] at ht; simp [hDx] at ht
      · exact (byLen_ct hΦ hD h16 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono (fun a b h => hback a b _ h) fun _ _ h => h

/-! ## The result and the check of `k` -/

/-- After the check of `k`: `x11` all ones iff `k < 2 hLen + 2`. -/
abbrev KReady (D : Nat) : Inv := fun L g vv m₀ t =>
  In L g vv m₀ (fun W t => W 32 = L.tabL ∧
    t.gpr .x11 = if 2 * D + 2 ≤ L.k.toNat then 0 else BitVec.allOnes 64) t

theorem resK_ct {H : Hash} (hD : H.D ≤ 64) {S : Nat} (hS : 15 ≤ S) (ts : List FnTable) (T : FnTable) (D : Nat) :
    RelCT isa (Two S ts (WithL ts T (LenI D)))
      (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK H))
      (Two S ts (WithL ts T (KReady H.D))) :=
  two [] (check_of_zImm (τ := Taint.ofRegs []) (c := .block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0,
    .str .x .x0 .x9 sR] : List Instr) ++ chkK H)) (c' := .block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0,
    .str .x .x0 .x9 sR] : List Instr) ++ chkK gH)) rfl (by taint_decide))
    (fun _ _ _ _ _ _ _ _ _ _ ⟨⟨c₁, _⟩, _⟩ ⟨⟨c₂, _⟩, _⟩ => ⟨c₁.sp.trans c₂.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun L g vv m₀ t hL hP h => by
      obtain ⟨⟨hcx, V, W, R, hS, h32, _⟩, _⟩ := id h
      have hP16 : 16 ≤ L.P := by omega_arith
      have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact WP.mono (Table.wp_sy (resK_ok (H := H) (hcx.lay hL hP16 R hS.scr) R hk3 hL.k1024 (by omega_arith)))
        fun u ⟨⟨_, S4, R4, x11⟩, sy⟩ => WithL.of h sy (In.of_step hL hP16 hcx S4 nil_ws R4
          (hS.of fun j _ _ h3 => by simp only [upd]; rw [ifn (by omega_arith)])
          ⟨by simp only [upd]; rw [ifn (by decide)]; exact h32, x11⟩)

/-! ## A short `k` -/

theorem zeroHead_ok {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (.block [.ldrSp .x11 sOut, .ldrSp .x12 sK, .movz .x .x13 0 0]) t fun u => u.sp = t.sp ∧
      u.gpr .x11 = L.out ∧ u.gpr .x12 = L.k ∧ u.gpr .x13 = 0 := by
  have Ly := hc.lay hL hP R hS.scr
  have h152 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 152) 8 := Ly.ld (d := 152) (by decide)
  have h168 : InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have ro := R.rd8 (d := 152) (k := 19) rfl (by decide) hS.out
  have rk := R.rd8 (d := 168) (k := 21) rfl (by decide) hS.k
  oaep_run [sOut, sK, h152, h168, Ly.sp, ro, rk]
  and_intros <;> first | trivial | rfl

theorem decFail_tr {S : Nat} (hS : 15 ≤ S) (e : Env) :
    RelCT isa (PW S e fun _ _ => True) decFail fun _ _ => True := by
  refine RelCT.seq (R := PW S e fun _ _ => True) (pw_seq (X' := fun _ _ => True) [.x11, .x12, .x13]
    (fun r => if r = .x11 then e.L.out else if r = .x12 then e.L.k else 0)
    (by taint_decide) (by taint_decide)
    (fun _ _ _ t _ _ hL hP hc R hS _ => WP.mono (zeroHead_ok hL (by omega_arith) hc R hS) fun u ⟨hs, x11, x12, x13⟩ =>
      ⟨hs, by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [*]⟩)
    fun g vv m₀ t V W hL hP hc R hS _ => ?_) ?_
  · have hP16 : 16 ≤ e.L.P := by omega_arith
    have Ly := hc.lay hL hP16 R hS.scr
    have O := hc.outAt hL hP16 hS
    have hk : W 21 = BitVec.ofNat 64 e.L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact WP.mono (zeroOut_ok Ly R O.ho hk (by have := hL.k64; omega_arith) hL.k1024 O.hw O.hnw O.ha)
      fun u ⟨_, Su, Ru, _⟩ => In.of_step hL hP16 hc Su (fun r h => by simp at h; exact .inl h) Ru hS trivial
  · show RelCT isa _ (.block ([.ldrSp .x11 sMl] ++ (.str .x .x13 .x11 0 :: faultBit))) _
    refine RelCT.block_append (pw_seq_tr [.x11] (fun _ => e.L.ml) (by taint_decide) (by taint_decide)
      fun g vv m₀ t V W hL hP hc R hS _ => ?_)
    have Ly := hc.lay hL (by omega_arith) R hS.scr
    have h216 : InRegions (t.rd ++ t.wr) (e.L.Q + BitVec.ofNat 64 216) 8 := Ly.ld (d := 216) (by decide)
    have rml := R.rd8 (d := 216) (k := 27) rfl (by decide) hS.ml
    oaep_run [sMl, h216, Ly.sp, rml]
    and_intros <;> first | trivial | rfl | (intro r hr; rw [List.mem_singleton.mp hr]; rfl)

end VG.Proof.RsaOaep.AArch64.Dec
