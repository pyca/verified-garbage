module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Compress
public import VerifiedGarbage.Proof.MdHashTable.AArch64
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.RsaPss.AArch64

/-!
# RSASSA-PSS on AArch64: the calls through the tables' slots

`scall args s ts` (`Impl/RsaPss/AArch64.lean`) runs as the call of the
function of `ts` whose address the slot `s` holds (`scall_wp`), and two runs
of it in which the slot holds the same address, which `ts` names the same
function in, as two runs of that call (`scall_rel`). The compression
function's call through its slot (`compT`) is then as the streaming code's
`compressAt` (`compT_ok`, `compT_rel`), and the digest's (`digestOut`) as
`digestK`'s call (`digT_ok`, `digT_rel`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_nil)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)

/-- The function an indirect call at `a` reaches, among `ts`. -/
abbrev Finds (ts : List (String × Prog isa)) (sy : String → Addr) (a : Addr) (n : String) (c : Prog isa) : Prop :=
  ts.find? (fun q => sy q.1 == a) = some (n, c)

theorem scall_wp {args : List Instr} {s : Nat} {ts : List (String × Prog isa)} {u : State} {n : String}
    {c : Prog isa} {Q : State → Prop} (hs : s % 8 = 0 ∧ s < 32768)
    (h : WP isa (.block args) u fun u₁ => InRegions (u₁.rd ++ u₁.wr) (u₁.sp + BitVec.ofNat 64 s) 8 ∧
      u₁.mem.readW (u₁.sp + BitVec.ofNat 64 s) 64 = u₁.syms n ∧ Finds ts u₁.syms (u₁.syms n) n c ∧
      ∀ u₂, Only [.x16] u₁ u₂ → u₂.syms = u₁.syms → WP isa (.call n c) u₂ Q) :
    WP isa (scall args s ts) u Q := by
  unfold scall
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms h fun u₁ ⟨hin, hw, hf, k⟩ _ => ?_
  refine WP.mono_syms (Q := fun u₂ => Only [.x16] u₁ u₂ ∧ u₂.gpr .x16 = u₁.mem.readW (u₁.sp + BitVec.ofNat 64 s) 64)
    (wp_ldrSp hs hin fun u₂ o e => wp_nil ⟨o, e⟩) fun u₂ ⟨o, e⟩ sy₂ => ?_
  refine WP.icalls_of_call (a := u₁.syms n) (by simp only [icall, e, hw]) ?_ (k u₂ o sy₂)
  show ts.find? (fun q => isa.fnAddr u₂ q.1 == u₁.syms n) = _
  simp only [isa]; rw [sy₂]; exact hf

/-- Two runs of `scall`: the block's states (`F`) in which `x16` holds the
same address, which names the same function `n` in both. -/
theorem scall_rel {args : List Instr} {s : Nat} {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    {P F : State → State → Prop}
    (ht : RelCT isa P (.block (args ++ ([.ldrSp .x16 s] : List Instr))) fun _ _ => True)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.block (args ++ ([.ldrSp .x16 s] : List Instr))) s₁ (F s₁) ∧
      WP isa (.block (args ++ ([.ldrSp .x16 s] : List Instr))) s₂ (F s₂))
    (hi : ∀ σ₁ σ₂ t₁ t₂, P σ₁ σ₂ → F σ₁ t₁ → F σ₂ t₂ → t₁.gpr .x16 = t₂.gpr .x16 ∧
      Finds ts t₁.syms (t₁.gpr .x16) n c ∧ Finds ts t₂.syms (t₂.gpr .x16) n c)
    (hc : RelCT isa (fun t₁ t₂ => ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ t₁ ∧ F σ₂ t₂) (.call n c) fun _ _ => True) :
    RelCT isa P (scall args s ts) fun _ _ => True := by
  unfold scall
  refine RelCT.seq ((ht.wpDep hw).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  cases ts with
  | nil =>
    exact RelCT.of_false fun t₁ t₂ ⟨σ₁, σ₂, hp, f₁, f₂⟩ => by
      have := (hi σ₁ σ₂ t₁ t₂ hp f₁ f₂).2.1; simp [Finds] at this
  | cons q ts =>
    refine RelCT.icalls_of_call hc fun t₁ t₂ ⟨σ₁, σ₂, hp, f₁, f₂⟩ => ?_
    obtain ⟨e, h₁, h₂⟩ := hi σ₁ σ₂ t₁ t₂ hp f₁ f₂
    refine ⟨t₁.gpr .x16, by simp only [icall], by simp only [icall, e], ?_, ?_, rfl⟩
    · show (q :: ts).find? (fun q => isa.fnAddr t₁ q.1 == t₁.gpr .x16) = _
      simp only [isa]; exact h₁
    · show (q :: ts).find? (fun q => isa.fnAddr t₂ q.1 == t₁.gpr .x16) = _
      simp only [isa]; rw [e]; exact h₂

/-! ## The compression function -/

section
open VG.Proof.Pbkdf2.AArch64 (CompOk CallOk CSetup csetup_ok call_pre c2_eq compK one_toNat)
open VG.Proof.MdStream (Md)

variable {B N L : Nat} {H : Md B N L} {so : Nat}

theorem csetup_only {s t u : State} (hs : CSetup s t) (o : Only [.x16] t u) : CSetup s u :=
  ⟨by rw [o.get .x0]; exact hs.x0, by rw [o.get .x1]; exact hs.x1, by rw [o.get .x2]; exact hs.x2,
    by rw [o.get .x3]; exact hs.x3, fun r hr => by
      rw [o.get r (by revert r; decide)]; exact hs.keep r hr,
    by rw [o.mem]; exact hs.mem, by rw [o.rd]; exact hs.rd, by rw [o.wr]; exact hs.wr, by rw [o.sp]; exact hs.sp⟩

/-- The call of the compression function, after its setup. -/
theorem comp_call {name : String} {code : Prog isa} (hf : CompOk H so code) {s t : State}
    {st scr src : Addr} (h : CallOk s N B so st scr src) (hs : CSetup s t)
    (hv : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) → Q s') :
    WP isa (.call name code) t Q := by
  have e := c2_eq (B := B) t hs.x2
  have hpre := call_pre (H := H) h hs
  rw [e] at hpre
  refine WP.callV (k := compK H so) hf.verified hpre ?_ ?_ ?_ hf.noFrames
  · rw [hs.rd, hs.wr]; simpa using h.cov
  · rw [hs.wr]; exact h.covW
  · intro s' hrd hwr hsp hfr hcs _ hvv hpost
    have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
    have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.x1.trans h.x1)
    have c2 : (t.callEntry.gpr .x2).toNat = 1 := by
      rw [State.callEntry_gpr _ (by decide), hs.x2, one_toNat]
    simp only [compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      hs.mem] at hpost
    rw [hs.mem] at hfr
    refine hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr h30 => (hcs r hr h30).trans (hs.keep r hr))
      (hsp.trans hs.sp) hfr ?_ fun r hr => (hvv r hr).trans (hv r hr)
    rw [hpost, Md.compressBlocks_one]

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`, by the function whose address the slot `sCmpH` holds. -/
theorem compT_ok (f : MdFns) {name : String} {code : Prog isa} (hf : CompOk H so code) {s : State}
    {st scr src : Addr} (h : CallOk s N B so st scr src)
    (hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 sCmpH) 8)
    (hw : s.mem.readW (s.sp + BitVec.ofNat 64 sCmpH) 64 = s.syms name)
    (hfd : Finds f.comp s.syms (s.syms name) name code) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) → Q s') :
    WP isa (compT f) s Q := by
  unfold compT
  refine scall_wp (n := name) (c := code) (by decide) (WP.mono_syms (WP.preservedV (csetup_ok s) (by lit_decide))
    fun t ⟨hs, hv⟩ sy => ?_)
  refine ⟨by rw [hs.rd, hs.wr, hs.sp]; exact hin, by rw [hs.mem, hs.sp, sy]; exact hw, by rw [sy]; exact hfd,
    fun u o _ => comp_call hf h (csetup_only hs o) (fun r hr => (o.vcs r hr).trans (hv r hr)) hQ⟩

/-- `compT` is constant time, in runs that call it on the same regions with
the same address in the slot, of the same function. -/
theorem compT_rel (f : MdFns) {name : String} {code : Prog isa} (hf : CompOk H so code) {st scr src : Addr}
    {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → CallOk s₁ N B so st scr src ∧ CallOk s₂ N B so st scr src ∧ s₁.sp = s₂.sp ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.sp + BitVec.ofNat 64 sCmpH) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.sp + BitVec.ofNat 64 sCmpH) 8 ∧
      s₁.mem.readW (s₁.sp + BitVec.ofNat 64 sCmpH) 64 = s₂.mem.readW (s₂.sp + BitVec.ofNat 64 sCmpH) 64 ∧
      Finds f.comp s₁.syms (s₁.mem.readW (s₁.sp + BitVec.ofNat 64 sCmpH) 64) name code ∧
      Finds f.comp s₂.syms (s₂.mem.readW (s₂.sp + BitVec.ofNat 64 sCmpH) 64) name code) :
    RelCT isa P' (compT f) fun _ _ => True := by
  have key : ∀ σ : State, InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 sCmpH) 8 →
      WP isa (.block ([mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20] ++ [.ldrSp .x16 sCmpH])) σ
        (fun t => CSetup σ t ∧ t.syms = σ.syms ∧ t.gpr .x16 = σ.mem.readW (σ.sp + BitVec.ofNat 64 sCmpH) 64) :=
    fun σ hin => by
      refine WP.mono_syms (Q := fun u => CSetup σ u ∧ u.gpr .x16 = σ.mem.readW (σ.sp + BitVec.ofNat 64 sCmpH) 64)
        ?_ fun u ⟨a, b⟩ sy => ⟨a, sy, b⟩
      rw [WP.block_append_iff]
      exact WP.mono (csetup_ok σ) fun t hs => wp_ldrSp (by decide) (by rw [hs.rd, hs.wr, hs.sp]; exact hin)
        fun u o e => wp_nil ⟨csetup_only hs o, by rw [e, hs.mem, hs.sp]⟩
  unfold compT
  refine scall_rel (n := name) (c := code) (F := fun σ t => CSetup σ t ∧ t.syms = σ.syms ∧
      t.gpr .x16 = σ.mem.readW (σ.sp + BitVec.ofNat 64 sCmpH) 64)
    (RelCT.taint (A := taint) (P := P') (Taint.ofRegs [])
      (fun s₁ s₂ hp => ⟨(hP s₁ s₂ hp).2.2.1, fun r hr => by simp at hr⟩) (by taint_decide))
    (fun s₁ s₂ hp => ⟨key s₁ (hP s₁ s₂ hp).2.2.2.1, key s₂ (hP s₁ s₂ hp).2.2.2.2.1⟩) ?_ ?_
  · intro σ₁ σ₂ t₁ t₂ hp ⟨_, sy₁, e₁⟩ ⟨_, sy₂, e₂⟩
    obtain ⟨-, -, -, -, -, he, f₁, f₂⟩ := hP σ₁ σ₂ hp
    exact ⟨by rw [e₁, e₂, he], by rw [sy₁, e₁]; exact f₁, by rw [sy₂, e₂]; exact f₂⟩
  refine RelCT.call (k := compK H so) hf.verified hf.ct [⟨src, B⟩] [⟨st, N⟩, ⟨scr, so⟩]
    fun t₁ t₂ ⟨σ₁, σ₂, hp, ⟨h₁, _, _⟩, ⟨h₂, _, _⟩⟩ => ?_
  obtain ⟨c₁, c₂, hsp, -⟩ := hP σ₁ σ₂ hp
  have p₁ := call_pre (H := H) c₁ h₁
  have p₂ := call_pre (H := H) c₂ h₂
  rw [c2_eq t₁ h₁.x2] at p₁
  rw [c2_eq t₂ h₂.x2] at p₂
  refine ⟨p₁, p₂, ?_, by rw [h₁.rd, h₁.wr]; simpa using c₁.cov, by rw [h₁.wr]; exact c₁.covW,
    by rw [h₂.rd, h₂.wr]; simpa using c₂.cov, by rw [h₂.wr]; exact c₂.covW⟩
  simp only [compK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    h₁.x0, h₂.x0, h₁.x1, h₂.x1, h₁.x2, h₂.x2, h₁.x3, h₂.x3, c₁.x19, c₂.x19, c₁.x1, c₂.x1, c₁.x20, c₂.x20,
    h₁.sp, h₂.sp, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end

/-! ## The digest -/

section
open VG.Proof.MdStream (Md)
open VG.Proof.MdHashTable.AArch64 (digestK digest_verified)
open VG.Impl.MdHashTable.AArch64 (digest)
open VG.Proof.MlKem.AArch64 (wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)

variable {P : Impl.Pbkdf2.AArch64.Params}

/-- What the calls of the digest of `P` need of its code, which the kernel
checks of each hash function: it keeps the callee-saved vector registers,
and it is constant time. -/
structure DigOK (P : Impl.Pbkdf2.AArch64.Params) : Prop where
  kv : (digest P).allInstrs keepsV = true
  ct : ∀ md : Md P.B P.N P.L, ConstantTime isa (digestK md).pre (digestK md).pub (digest P)

/-- The arguments of the digest, and the address of its slot in `x16`. -/
structure DSetup (u t : State) : Prop where
  x0 : t.gpr .x0 = u.gpr .x20 + BitVec.ofNat 64 oSel
  x1 : t.gpr .x1 = u.gpr .x21
  x16 : t.gpr .x16 = u.mem.readW (u.sp + BitVec.ofNat 64 sDigH) 64
  only : Only [.x0, .x1, .x16] u t
  syms : t.syms = u.syms

theorem dsetup_ok {u : State} (hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sDigH) 8) :
    WP isa (.block (([.addImm .x .x0 .x20 oSel, mov .x1 .x21] : List Instr) ++
      ([.ldrSp .x16 sDigH] : List Instr))) u (DSetup u) := by
  refine WP.mono_syms (Q := fun t => t.gpr .x0 = u.gpr .x20 + BitVec.ofNat 64 oSel ∧ t.gpr .x1 = u.gpr .x21 ∧
    t.gpr .x16 = u.mem.readW (u.sp + BitVec.ofNat 64 sDigH) 64 ∧ Only [.x0, .x1, .x16] u t) ?_
    fun t ⟨a, b, c, d⟩ sy => ⟨a, b, c, d, sy⟩
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => ?_
  refine wp_ldrSp (by decide) (by rw [o₂.rd, o₂.wr, o₂.sp, o₁.rd, o₁.wr, o₁.sp]; exact hin) fun t o₃ e₃ => wp_nil ?_
  refine ⟨by rw [o₃.get .x0, o₂.get .x0, e₁], by rw [o₃.get .x1, e₂, o₁.get .x21],
    by rw [e₃, o₂.mem, o₂.sp, o₁.mem, o₁.sp], (o₁.trans (o₂.trans o₃)).mono⟩

/-- The pre of the digest's call. -/
theorem dig_pre (md : Md P.B P.N P.L) {t : State} {vp op : Addr} (h0 : t.gpr .x0 = vp) (h1 : t.gpr .x1 = op)
    (hd : Region.Disjoint ⟨vp, P.N⟩ ⟨op, P.N⟩) :
    (digestK md).pre (t.callEntry.withRegions [⟨vp, P.N⟩] [⟨op, P.N⟩]) := by
  simp only [digestK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    h0, h1]
  exact ⟨trivial, trivial, hd⟩

/-- The digest of the hash value at `scratch + oSel` (`vp`) to `x21` (`op`),
by the function whose address the slot `sDigH` holds. -/
theorem digT_ok (f : MdFns) {md : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape md) (hd : DigOK P) {dn : String} {u : State}
    {vp op : Addr} (hin : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sDigH) 8)
    (hw : u.mem.readW (u.sp + BitVec.ofNat 64 sDigH) 64 = u.syms dn) (hfd : Finds f.dig u.syms (u.syms dn) dn (digest P))
    (h0 : u.gpr .x20 + BitVec.ofNat 64 oSel = vp) (h1 : u.gpr .x21 = op)
    (hrd : Covers [⟨vp, P.N⟩] (u.rd ++ u.wr)) (hwr : Covers [⟨op, P.N⟩] u.wr)
    (hdis : Region.Disjoint ⟨vp, P.N⟩ ⟨op, P.N⟩) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = u.rd → s'.wr = u.wr → s'.sp = u.sp → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) →
      s'.mem = WriteBytes.writeBytes u.mem op (md.digest (md.stateAt u.mem vp)) → Q s') :
    WP isa (digestOut f) u Q := by
  unfold digestOut
  refine scall_wp (n := dn) (c := digest P) (by decide) (WP.mono_syms
    (Q := fun u₁ => Only [.x0, .x1] u u₁ ∧ u₁.gpr .x0 = vp ∧ u₁.gpr .x1 = op)
    (wp_addImm (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ =>
      wp_nil ⟨(o₁.trans o₂).mono, by rw [o₂.get .x0, e₁, h0], by rw [e₂, o₁.get .x21, h1]⟩)
    fun u₁ ⟨o, e0, e1⟩ sy => ⟨by rw [o.rd, o.wr, o.sp]; exact hin, by rw [o.mem, o.sp, sy]; exact hw,
      by rw [sy]; exact hfd, fun u₂ o₂ _ => ?_⟩)
  have g0 : u₂.gpr .x0 = vp := by rw [o₂.get .x0, e0]
  have g1 : u₂.gpr .x1 = op := by rw [o₂.get .x1, e1]
  refine WP.callV (k := digestK md) (digest_verified hs hd.kv) (dig_pre md g0 g1 hdis) ?_ ?_ ?_ rfl
  · rw [o₂.rd, o₂.wr, o.rd, o.wr]; exact Covers.append_left hrd (Covers.right hwr)
  · rw [o₂.wr, o.wr]; exact hwr
  · intro s' hr hw' hsp _ hcs _ hv hpost
    simp only [digestK, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      g0, g1] at hpost
    refine hQ s' (by rw [hr, o₂.rd, o.rd]) (by rw [hw', o₂.wr, o.wr]) (by rw [hsp, o₂.sp, o.sp])
      (fun r hr' h30 => by
        rw [hcs r hr' h30, o₂.get r (by revert r; decide), o.get r (by revert r; decide)])
      (fun r hr' => by rw [hv r hr', o₂.vcs r hr', o.vcs r hr']) (by rw [hpost, o₂.mem, o.mem])

/-- Two runs of `digestOut` with the same arguments, in which the slot holds
the same address, of the same function. -/
theorem digT_rel (f : MdFns) {md : Md P.B P.N P.L} (hs : VG.Proof.Pbkdf2.AArch64.Shape md) (hd : DigOK P) {dn : String}
    {vp op : Addr} {P' : State → State → Prop}
    (hP : ∀ u₁ u₂, P' u₁ u₂ → u₁.sp = u₂.sp ∧
      InRegions (u₁.rd ++ u₁.wr) (u₁.sp + BitVec.ofNat 64 sDigH) 8 ∧
      InRegions (u₂.rd ++ u₂.wr) (u₂.sp + BitVec.ofNat 64 sDigH) 8 ∧
      u₁.mem.readW (u₁.sp + BitVec.ofNat 64 sDigH) 64 = u₂.mem.readW (u₂.sp + BitVec.ofNat 64 sDigH) 64 ∧
      Finds f.dig u₁.syms (u₁.mem.readW (u₁.sp + BitVec.ofNat 64 sDigH) 64) dn (digest P) ∧
      Finds f.dig u₂.syms (u₂.mem.readW (u₂.sp + BitVec.ofNat 64 sDigH) 64) dn (digest P) ∧
      u₁.gpr .x20 + BitVec.ofNat 64 oSel = vp ∧ u₁.gpr .x21 = op ∧
      u₂.gpr .x20 + BitVec.ofNat 64 oSel = vp ∧ u₂.gpr .x21 = op ∧
      Covers [⟨vp, P.N⟩] (u₁.rd ++ u₁.wr) ∧ Covers [⟨op, P.N⟩] u₁.wr ∧
      Covers [⟨vp, P.N⟩] (u₂.rd ++ u₂.wr) ∧ Covers [⟨op, P.N⟩] u₂.wr ∧
      Region.Disjoint ⟨vp, P.N⟩ ⟨op, P.N⟩) :
    RelCT isa P' (digestOut f) fun _ _ => True := by
  unfold digestOut
  refine scall_rel (n := dn) (c := digest P) (F := DSetup)
    (RelCT.taint (A := taint) (P := P') (Taint.ofRegs [.x20, .x21])
      (fun s₁ s₂ hp => ⟨(hP s₁ s₂ hp).1, fun r hr => by
        simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨-, -, -, -, -, -, a₁, b₁, a₂, b₂, -⟩ := hP s₁ s₂ hp
        rcases hr with rfl | rfl
        · have h := a₁.trans a₂.symm; simpa using h
        · rw [b₁, b₂]⟩) (by taint_decide))
    (fun s₁ s₂ hp => ⟨dsetup_ok (hP s₁ s₂ hp).2.1, dsetup_ok (hP s₁ s₂ hp).2.2.1⟩) ?_ ?_
  · intro σ₁ σ₂ t₁ t₂ hp d₁ d₂
    obtain ⟨-, -, -, he, f₁, f₂, -⟩ := hP σ₁ σ₂ hp
    exact ⟨by rw [d₁.x16, d₂.x16, he], by rw [d₁.syms, d₁.x16]; exact f₁, by rw [d₂.syms, d₂.x16]; exact f₂⟩
  refine RelCT.call (k := digestK md) (digest_verified hs hd.kv) (hd.ct md) [⟨vp, P.N⟩] [⟨op, P.N⟩]
    fun t₁ t₂ ⟨σ₁, σ₂, hp, d₁, d₂⟩ => ?_
  obtain ⟨hsp, -, -, -, -, -, a₁, b₁, a₂, b₂, r₁, w₁, r₂, w₂, hdis⟩ := hP σ₁ σ₂ hp
  have g0 : t₁.gpr .x0 = vp := by rw [d₁.x0, a₁]
  have g1 : t₁.gpr .x1 = op := by rw [d₁.x1, b₁]
  have g0' : t₂.gpr .x0 = vp := by rw [d₂.x0, a₂]
  have g1' : t₂.gpr .x1 = op := by rw [d₂.x1, b₂]
  refine ⟨dig_pre md g0 g1 hdis, dig_pre md g0' g1' hdis, ?_,
    by rw [d₁.only.rd, d₁.only.wr]; exact Covers.append_left r₁ (Covers.right w₁),
    by rw [d₁.only.wr]; exact w₁,
    by rw [d₂.only.rd, d₂.only.wr]; exact Covers.append_left r₂ (Covers.right w₂),
    by rw [d₂.only.wr]; exact w₂⟩
  simp only [digestK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    g0, g1, g0', g1', d₁.only.sp, d₂.only.sp, hsp]
  exact ⟨trivial, trivial, trivial⟩

end

/-! ## The slots of the table of `MdHash` -/

/-- The slots of the table of `MdHash` in the frame at `F`, in the memory
`m`, hold the addresses `sy` gives `H`'s `init`, compression function and
digest (`dn`, whose code is `digest H.P`), which the calls of `f` reach. -/
structure HT (H : Impl.Pbkdf2.Md.AArch64.Hash) (dn : String) (f : MdFns) (F : Addr) (m : Mem)
    (sy : String → Addr) : Prop where
  wi : m.readW (off F sIniH) 64 = sy H.initN
  wc : m.readW (off F sCmpH) 64 = sy H.compN
  wd : m.readW (off F sDigH) 64 = sy dn
  fi : Finds f.init sy (sy H.initN) H.initN H.initC
  fc : Finds f.comp sy (sy H.compN) H.compN H.compC
  fd : Finds f.dig sy (sy dn) dn (Impl.MdHashTable.AArch64.digest H.P)

/-- The slots, after writes apart from the frame. -/
theorem HT.keep {H : Impl.Pbkdf2.Md.AArch64.Hash} {dn : String} {f : MdFns} {F : Addr} {m m' : Mem}
    {sy : String → Addr} (h : HT H dn f F m sy) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨F, frameBytes⟩ r) : HT H dn f F m' sy := by
  have k : ∀ d, d + 8 ≤ frameBytes → m'.readW (off F d) 64 = m.readW (off F d) 64 := fun d hd' =>
    hf.readW (r := ⟨off F d, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base F (by unfold frameBytes at *; omega))) (by decide)
  exact ⟨(k _ (by decide)).trans h.wi, (k _ (by decide)).trans h.wc, (k _ (by decide)).trans h.wd, h.fi, h.fc,
    h.fd⟩

end VG.Proof.RsaPss.AArch64
