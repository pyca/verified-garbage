module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Impl.RsaOaep.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaOaep.X86.Calls
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtXor
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86.Base

/-!
# RSAES-OAEP on x86: the indirect calls of a table's functions

`tcall_vp`: the call of a table's function `j` (`Impl.RsaOaep.X86.tcall`:
its address into `esi`, then `call esi` in the frame of its arguments) is a
piece (`VP`) as the call of the function it reaches is in that frame, when
both runs reach it at the same address, with the same `esp`. `VP.syms`: a
piece keeps the addresses of the statics, which the calls need to know
which function the table's address names.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaOaep.X86 (tcall sTab)
open VG.Impl.RsaPss.X86 (ld)
open VG.Impl.RsaPkcs1Sig.X86 (at_)

/-- A piece keeps the addresses of the statics. -/
theorem VP.syms {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) :
    VP (fun σ s => F σ s ∧ s.syms = σ.syms) c (fun σ s => G σ s ∧ s.syms = σ.syms) := by
  refine ⟨fun σ s hs => WP.mono_syms (h.wp σ s hs.1) fun _ hq sy => ⟨hq, sy.trans hs.2⟩, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨h₁, y₁⟩, ⟨h₂, y₂⟩⟩ e₁ e₂
  have r := ((h.ct.mono (P' := fun a b => F σ₁ a ∧ F σ₂ b) (fun a b hab => ⟨σ₁, σ₂, hab⟩) fun _ _ q => q).wp
    (F₁ := G σ₁) (F₂ := G σ₂) fun _ _ hh => ⟨h.wp _ _ hh.1, h.wp _ _ hh.2⟩) _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, ⟨r.2.2.1, (Exec.syms e₁).trans y₁⟩, ⟨r.2.2.2, (Exec.syms e₂).trans y₂⟩⟩

/-- The call of the table's function `j`, among `ts`, in a frame pushing
`rs`: after the load of its address into `esi` (`hl`), it reaches `(n, c)`
(`ht`), at the same address in both runs, with the same `esp` (`hpub`). -/
theorem tcall_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg}
    {n : String} {c : Prog isa} (hne : ts ≠ [])
    (hl : VP F (.block [ld .esi sTab, .mov .esi (.mem (at_ .esi (4 * j)))]) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .esi).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .esi = s₂.gpr .esi ∧ s₁.gpr .esp = s₂.gpr .esp)
    (h : VP F₁ (.frame (.push rs) (.call n c) (.pop .eax rs.length)) G) : VP F (tcall j ts rs) G := by
  have tgt : ∀ σ s u, F₁ σ s → isa.push (.push rs) s = some u →
      icallTarget isa u ((u.gpr .esi).setWidth 64) ts = some (n, c) := fun σ s u hs hp => by
    obtain ⟨-, -, -, rfl⟩ := push_some hp
    rw [pushed_gpr _ _ (by decide), icallTarget_congr (s₂ := s) fun q _ => by
      show ((pushed rs s).syms q.1).setWidth 64 = (s.syms q.1).setWidth 64
      rw [show (pushed rs s).syms = s.syms from pushRegs_syms s rs]]
    exact ht σ s hs
  refine VP.seq hl ⟨fun σ s hs => WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, tgt σ s u hs hp⟩) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.frame_icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
  · show addrs (.push rs) s₁ = addrs (.push rs) s₂
    simp only [addrs, (hpub _ _ _ _ h₁ h₂).2]
  · obtain ⟨-, -, -, rfl⟩ := push_some hp₁
    obtain ⟨-, -, -, rfl⟩ := push_some hp₂
    have e₁ := tgt σ₁ s₁ _ h₁ hp₁
    have e₂ := tgt σ₂ s₂ _ h₂ hp₂
    have g : (pushed rs s₂).gpr .esi = (pushed rs s₁).gpr .esi := by
      rw [pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), (hpub _ _ _ _ h₁ h₂).1]
    rw [g] at e₂
    exact ⟨_, rfl, congrArg (fun v => some (BitVec.setWidth 64 v)) g, e₁, e₂, rfl⟩

end VG.Proof.RsaOaep.X86

/-!
# RSAES-OAEP on x86: `dst ⊕= MGF1(src, dstLen)`, with MGF1's table

`mgf_vp`: with `src` (`sl` bytes at `so`) and `dst` (`dl` bytes at `dOff`)
in `EM`'s place in our part of `scratch` (from `oEm` to `oBuf`), their
addresses and lengths in their slots, `mgfXor f j` XORs MGF1's mask of
`src` into `dst`, one digest of `src ‖ C` (by the streaming `init`, two
`update`s and `finalize`) at a time, as on ARMv7
(`Proof/RsaOaep/Arm/Mgf.lean`), with the hash function `g` of the table
that is our argument `j` (at `p`, `L.argv`'s word `j`): in every run, the
table holds `g`'s functions' addresses (`ai`, `au`, `af`, the same in both
runs) and its digest length (`TabFacts`), and an indirect call of `f`'s
functions to their address reaches them (`TabOK`), so each call through the
table (`tcall_vp`) runs as `g`'s (`tcallK_vp`). The table's address and
digest length are in their slots (`sTab`, `sHl`) during the rounds, and
every stage keeps the addresses of the statics (`VP.syms`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (oCW oSt oDig oEm oRsa frameBytes countLoop sCtr sDone xorBody mgfInit)
open VG.Proof.RsaPss.X86.Sg (vpAssoc)

open VG.Impl.RsaOaep.X86 (Fns tcall sTab sHl tabArgs)

/-! ## The table -/

/-- At `p` in `m`, the addresses `sy` gives `G`'s `init`, `update` and
`finalize`. -/
def TabMem (G : Impl.Pbkdf2.Stream.X86.Hash) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (VG.X86.addr p 0) 32 = sy G.initN ∧ m.readW (VG.X86.addr p 4) 32 = sy G.updN ∧
    m.readW (VG.X86.addr p 8) 32 = sy G.finN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `G`'s functions reaches it. -/
structure TabOK (G : Impl.Pbkdf2.Stream.X86.Hash) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy G.initN).setWidth 64) = some (G.initN, G.initC)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy G.updN).setWidth 64) = some (G.updN, G.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy G.finN).setWidth 64) = some (G.finN, G.finC)

/-- What MGF1 needs of its table at `p`, in the run from `σ`: an indirect
call reaches `G`'s functions, at `ai`, `au` and `af`, whose addresses the
table holds, then its digest length. -/
structure TabFacts (G : Impl.Pbkdf2.Stream.X86.Hash) (f : Fns) (p ai au af : BitVec 32) (σ : State) : Prop where
  ok : TabOK G f σ.syms
  mem : TabMem G σ.syms p σ.mem
  d : σ.mem.readW (VG.X86.addr p 16) 32 = BitVec.ofNat 32 G.D
  ai : σ.syms G.initN = ai
  au : σ.syms G.updN = au
  af : σ.syms G.finN = af

/-- A word of a buffer only read, as on entry. -/
theorem St_roW {L : Lay} {σ s : State} (h : L.St σ s) {R : Region} (hR : R ∈ L.ro) {a : Addr}
    (hc : R.Contains a 4) : s.mem.readW a 32 = σ.mem.readW a 32 := by
  refine h.frame.readW hc (fun r hr => ?_) (by decide)
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (h.ok.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `sub d, [b + o]`, and the carry flag. -/
theorem wp_subm_cf {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) →
      s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

variable {L : Lay} {scr : BitVec 32} (g : OHash) {f : Fns} {j : Nat} {ai au af : BitVec 32}

/-- The bytes at `scr + o` as a list. -/
theorem bytesAt_scr (hg : Geo L scr) {m : Mem} {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) {xs : List Byte}
    (hl : xs.length = n) (hx : ∀ i < n, m (sa scr (o + i)) = xs.getD i 0) :
    Spec.Sha256.bytesAt m ((scr + BitVec.ofNat 32 o).setWidth 64) n = xs := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  have e := hx i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e
  rw [← e, hg.scrA (by omega_arith), sa, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The parameters -/

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (dOff dl : Nat) : List Region :=
  [sR scr oSt g.H.S, sR scr oCtr 4, sR scr oDig g.H.F, sR scr oCW g.ok.Wb, L.LOW, sR scr dOff dl, slotR L sCtr,
    slotR L sDone, slotR L sTab, slotR L sHl]

/-- The parameters of `mgfXor f j`: `src` (`sl` bytes at `so`) and `dst`
(`dl` bytes at `dOff`), apart, in `EM`'s place; their slots, what the caller
keeps (`Inv`), and the table that is our argument `j`: in a buffer only
read (`tR`), with what MGF1 needs of it in every run (`tab`). -/
structure MP (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (f : Fns) (j : Nat) (ai au af : BitVec 32) : Prop where
  hg : Geo L scr
  sl0 : 0 < sl
  dl0 : 0 < dl
  so0 : oEm ≤ so
  do0 : oEm ≤ dOff
  fs : so + sl ≤ oBuf
  fd : dOff + dl ≤ oBuf
  sep : so + sl ≤ dOff ∨ dOff + dl ≤ so
  sd : ∀ σ, (seed σ).length = sl
  I : ∀ σ m m', Inv σ m → Frame (mgfW g L scr dOff dl) m m' → Inv σ m'
  src : ∀ σ m, Inv σ m → m.readW (L.fr sSrc) 32 = scr + BitVec.ofNat 32 so
  srcL : ∀ σ m, Inv σ m → m.readW (L.fr sSrcLen) 32 = BitVec.ofNat 32 sl
  dst : ∀ σ m, Inv σ m → m.readW (L.fr sDst) 32 = scr + BitVec.ofNat 32 dOff
  dstL : ∀ σ m, Inv σ m → m.readW (L.fr sDstLen) 32 = BitVec.ofNat 32 dl
  hj : j < L.argv.length
  tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (VG.X86.addr (L.argv.getD j 0) o) 4
  cA : TaintOk [.esp, .ebp] (.block [Impl.RsaPss.X86.ld .eax (Impl.RsaPss.X86.arg j), Impl.RsaPss.X86.st .eax sTab])
  tab : ∀ σ m, Inv σ m → TabFacts g.H f (L.argv.getD j 0) ai au af σ
  fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []

/-- The memory before iteration `c`: the counter, the bytes masked, `dst`
masked up to `c hLen` bytes, and `src`. -/
structure MB (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  tabS : m.readW (L.fr sTab) 32 = L.argv.getD j 0
  hlS : m.readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

variable {so sl dOff dl : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dstv : State → Nat → Byte}

/-- What the caller keeps, and the memory before iteration `c`. -/
abbrev MI (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : State → Nat → Byte)
    (seed : State → List Byte) (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  Inv σ m ∧ MB g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) m

/-- What misses the slots of the counter and of the bytes masked, `dst` and `src`. -/
abbrev Away (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (r : Region) : Prop :=
  (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧ (sR scr dOff dl).Disjoint r ∧ (sR scr so sl).Disjoint r ∧
    (slotR L sTab).Disjoint r ∧ (slotR L sHl).Disjoint r

namespace MP

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af)
include P

theorem keepB {c : Nat} {dv : Nat → Byte} {sd : List Byte} {m m' : Mem} {rs : List Region}
    (hm : MB g (j := j) L scr so sl dOff dl c dv sd m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) : MB g (j := j) L scr so sl dOff dl c dv sd m' := by
  have := P.fs; have := P.fd
  exact ⟨slot_keep hf (fun r hr => (hs r hr).2.2.2.2.1) hm.tabS, slot_keep hf (fun r hr => (hs r hr).2.2.2.2.2) hm.hlS,
    slot_keep hf (fun r hr => (hs r hr).1) hm.ctr, slot_keep hf (fun r hr => (hs r hr).2.1) hm.done,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.1) (by oomega) hm.dx,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.2.1) (by oomega) hm.sd⟩

theorem keep {c : Nat} {σ : State} {m m' : Mem} {rs : List Region}
    (hm : MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m) (hf : Frame rs m m')
    (hsub : ∀ r ∈ rs, r ∈ mgfW g L scr dOff dl) (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) :
    MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m' :=
  ⟨P.I σ m m' hm.1 (hf.mono hsub), P.keepB hm.2 hf hs⟩

/-- A range of our part of `scratch` before `EM` misses them. -/
theorem away_lo {o n : Nat} (hn : o + n ≤ oEm) : Away L scr so sl dOff dl (sR scr o n) := by
  have := P.fs; have := P.fd; have := P.so0; have := P.do0
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide), P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide),
    Geo.sep (by oomega) (by oomega) (by oomega), Geo.sep (by oomega) (by oomega) (by oomega),
    P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide), P.hg.slot ok (by oomega) (by rw [P.hg.F]; decide)⟩

theorem away_low : Away L scr so sl dOff dl L.LOW := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega_arith
  exact ⟨Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC, P.hg.low ok (by oomega), P.hg.low ok (by oomega),
    Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC⟩

/-- So does a slot other than theirs. -/
theorem away_slot {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d)
    (h₂ : d + 4 ≤ sTab ∨ sHl + 4 ≤ d) : Away L scr so sl dOff dl (slotR L d) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [P.hg.F]; omega_arith
  refine ⟨slotSep (by decide) hd (by unfold sCtr sDone at *; omega_arith),
    slotSep (by decide) hd (by unfold sCtr sDone at *; omega_arith), (P.hg.slot ok (by oomega) hF).symm,
    (P.hg.slot ok (by oomega) hF).symm, slotSep (by decide) hd (by unfold sTab sHl at *; omega_arith),
    slotSep (by decide) hd (by unfold sTab sHl at *; omega_arith)⟩

end MP

/-- The counter's bytes at `oCtr`. -/
abbrev Cb (scr : BitVec 32) (c : Nat) (m : Mem) : Prop := ∀ i < 4, m (sa scr (oCtr + i)) = (Spec.Rsa.i2osp c 4).getD i 0

/-- The digest of `src ‖ C` at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < g.H.D, m (sa scr (oDig + i)) = (g.ok.SH.H.hash x).getD i 0

/-- The memory after the XOR of iteration `c`. -/
structure DX (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  tabS : m.readW (L.fr sTab) 32 = L.argv.getD j 0
  hlS : m.readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D + g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

theorem UArgs.esi {scr d : BitVec 32} {len c : Nat} {s t : State} {v : BitVec 32} (h : UArgs scr d len c s)
    (u : Upd s t .esi v) : UArgs scr d len c t :=
  ⟨(u.other _ (by decide)).trans h.ebx, (u.other _ (by decide)).trans h.edi, (u.other _ (by decide)).trans h.eax,
    (u.other _ (by decide)).trans h.edx, (u.other _ (by decide)).trans h.ecx⟩

theorem FArgs.esi {scr : BitVec 32} {o c : Nat} {s t : State} {v : BitVec 32} (h : FArgs scr o c s)
    (u : Upd s t .esi v) : FArgs scr o c t :=
  ⟨(u.other _ (by decide)).trans h.ebx, (u.other _ (by decide)).trans h.eax, (u.other _ (by decide)).trans h.ecx,
    (u.other _ (by decide)).trans h.edx⟩

/-! ## A call through the table -/

section TCall

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af) (c : Nat)
include P

/-- The call of the table's function `k`, among `ts`, in a frame pushing
`rs`, from a stage with `Ctx`, MGF1's memory before iteration `c` and `X`,
which an update of `esi` keeps: as the call of `n`, at `a` in every run, in
that frame. -/
theorem tcallK_vp {X : State → State → Prop} (hX : ∀ σ s t v, X σ s → Upd s t .esi v → X σ t) {k : Nat}
    (hk3 : k < 3) {ts : List (String × Prog isa)} {rs : List Reg} {n : String} {cn : Prog isa}
    {a : BitVec 32} (hne : ts ≠ [])
    (ha : ∀ σ, TabFacts g.H f (L.argv.getD j 0) ai au af σ →
      σ.mem.readW (VG.X86.addr (L.argv.getD j 0) (4 * k)) 32 = a ∧ σ.syms n = a ∧
        ts.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms n).setWidth 64) = some (n, cn))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
      s.syms = σ.syms) (.frame (.push rs) (.call n cn) (.pop .eax rs.length)) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms)
      (tcall k ts rs) G := by
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  have hk : 4 * k + 4 ≤ 20 := by omega
  obtain ⟨tR, tRo, tC⟩ := P.tbl
  let F : State → State → Prop := fun σ s =>
    (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms
  have keepF : ∀ σ s t v, F σ s → Upd s t .esi v → F σ t := fun σ s t v ⟨⟨hc, hm, hx⟩, sy⟩ u =>
    ⟨⟨hc.upd u (by decide) (by decide), u.mem ▸ hm, hX σ s t v hx u⟩, u.syms.trans sy⟩
  refine tcall_vp (F₁ := fun σ s => F σ s ∧ s.gpr .esi = a) hne ?_ ?_ ?_
    (h.mono (fun σ s hs => hs.1) fun _ _ h => h)
  · show VP F (.block ([Impl.RsaPss.X86.ld .esi sTab] ++ [.mov .esi (.mem (Impl.RsaPkcs1Sig.X86.at_ .esi (4 * k)))]))
      (fun σ s => F σ s ∧ s.gpr .esi = a)
    refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .esi = L.argv.getD j 0)
      (VP.taint [.esp, .ebp] tload_taint (sp_bp fun _ _ h => h.1.1) fun σ s hs => ?_)
      (VP.taint [.esp, .ebp, .esi] (tword_taint hk3) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    · simp only [Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.stk]
      refine hs.1.1.wp_slot hg (by decide) (by decide) (by decide) fun t1 _ u1 => WP.block_nil ⟨keepF σ s t1 _ hs u1, ?_⟩
      rw [u1.gpr, hs.1.2.1.2.tabS]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]
      · rw [h₁.1.1.1.ebp, h₂.1.1.1.ebp]
      · rw [h₁.2, h₂.2]
    · obtain ⟨hF, hsi⟩ := hs
      have T := P.tab σ _ hF.1.2.1.1
      have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr (L.argv.getD j 0) (4 * k)) 4 :=
        ⟨tR, hF.1.1.st.inRo tRo, tC _ hk⟩
      refine wp_ldm (B := L.argv.getD j 0) hsi hin fun t2 u2 => WP.block_nil ⟨keepF σ s t2 _ hF u2, ?_⟩
      rw [u2.gpr, St_roW hF.1.1.st tRo (tC _ hk), (ha σ T).1]
  · intro σ s ⟨hF, hsi⟩
    have T := P.tab σ _ hF.1.2.1.1
    obtain ⟨-, hn, hf⟩ := ha σ T
    show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .esi).setWidth 64) = some (n, cn)
    rw [hsi, hF.2, ← hn]
    exact hf
  · intro σ₁ σ₂ s₁ s₂ h₁ h₂
    exact ⟨h₁.2.trans h₂.2.symm, h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm⟩

end TCall

/-! ## The stages of an iteration -/

section Iter

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af) (c : Nat)
include P

/-- The state set to the empty message. -/
theorem mgfA_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
      (.seq (.block initArgs) (callInit f))
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) []) ∧ s.syms = σ.syms) := by
  have := g.S_le
  have hI : ∀ σ m m', MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m → Frame [sR scr oSt g.H.S, L.LOW] m m' →
      MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m' := fun σ m m' hm hf =>
    P.keep hm hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.away_lo (by oomega)
      · exact P.away_low
  refine VP.seq (VP.syms initArgs_vp) ?_
  refine tcallK_vp P c (X := fun _ s => s.gpr .ebx = scr + BitVec.ofNat 32 oSt)
    (fun _ _ _ _ h u => (u.other .ebx (by decide)).trans h) (k := 0) (by decide) P.fne.1 (a := ai)
    (fun σ T => ⟨T.mem.1.trans T.ai, T.ai, T.ok.i⟩) ?_
  exact (VP.syms (initCall_vp P.hg g.H g.ok hI)).mono (fun σ s ⟨⟨hc, hm, hb⟩, sy⟩ => ⟨⟨hc, hm, hb⟩, sy⟩)
    fun _ _ h => h

/-- `update(state, 0, src, sl)`'s arguments. -/
theorem mgfB_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [])
      (.block updSrcArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) := by
  have hg := P.hg
  have := P.fs
  refine VP.taint [.esp, .ebp] updSrcArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => ?_
  have c4 : Ctx L scr σ t4 := (((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3
    (by decide) (by decide)).upd u4 (by decide) (by decide)
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 =>
    c5.wp_slot hg (by decide) (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
  have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, m4]
  refine ⟨c6, m6 ▸ hm, m6 ▸ rp, rfl, by rw [m6]; exact bytesAt_scr hg (by oomega) P.sl0 (P.sd σ) hm.2.sd,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr, m4, P.src σ _ hm.1]
  · rw [u6.gpr, u5.mem, m4, P.srcL σ _ hm.1]

/-- `update` absorbs `src`. -/
theorem mgfC_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
      (hUpd g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) := by
  have hg := P.hg
  have := P.fs; have := P.so0; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aS : (scr + BitVec.ofNat 32 so).setWidth 64 = sa scr so := hg.scrA (by have := P.sl0; oomega)
  refine upd_vp hg g.H g.ok (msg := fun _ => []) (dat := seed) (c := 0) (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv)
    (hg.rbuf (o := so) (n := sl) (by oomega) P.sl0)
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aS]; exact hg.low ok (by oomega))
    (by decide) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low

/-- `update` absorbs `src`, through the table. -/
theorem mgfC_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) ∧ s.syms = σ.syms)
      (callUpd f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
      Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 so).setWidth 64) sl = seed σ ∧
      UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
    (fun _ _ _ _ ⟨r, l, b, ua⟩ u => ⟨u.mem ▸ r, l, u.mem ▸ b, ua.esi u⟩) (k := 1) (by decide) P.fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩) (VP.syms (mgfC_call P c))

/-- The counter, big-endian, at `oCtr`. -/
theorem mgfD_vp (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ))
      (.block ctrSet)
      (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le
  have fit := hg.fit
  unfold oRsa at fit
  refine VP.taint [.esp, .ebp] ctrSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  simp only [ctrSet, Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.at_]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_bswap fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := c1.upd u2 (by decide) (by decide)
  have aW : VG.X86.addr scr oCtr = sa scr oCtr := hg.scrA (by oomega)
  refine wp_stm (B := scr) c2.ebp (by rw [aW]; exact hg.wr c2.st (by oomega)) fun t3 u3 => WP.block_nil ?_
  have e2 : t2.gpr .eax = bswap (BitVec.ofNat 32 c) := by rw [u2.gpr, u1.gpr, hm.2.ctr]
  have m3 : t3.mem = s.mem.writeW (sa scr oCtr) (bswap (BitVec.ofNat 32 c)) := by
    rw [u3.mem, aW, e2, u2.mem, u1.mem]
  have fr : Frame [sR scr oCtr 4] s.mem t3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by oomega) (by oomega) (by oomega))
  refine ⟨ctxW hg hc fr (fun r hr => .inl ⟨oCtr, 4, by oomega, by simpa using hr⟩) (by rw [u3.rd, u2.rd, u1.rd])
      (by rw [u3.wr, u2.wr, u1.wr]) (by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide)])
      (by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide)]),
    ⟨P.keep hm fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact P.away_lo (by oomega),
      g.ok.repr _ _ _ _ _ (fun i hi => ?_) rp⟩, fun i hi => ?_⟩
  · exact fr.bytes (R := sR scr oSt g.H.S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega))
      (by show g.H.S ≤ 2 ^ 64; omega_arith) hi
  rw [m3, sa_writeW32 scr _ _ (by oomega) (by oomega), ite_eq_left (by omega_arith),
    show oCtr + i - oCtr = i by omega_arith, ctrByte hc32 hi, i2osp4_getD c _ hi]

/-- `update(state, sl, scratch + oCtr, 4)`'s arguments. -/
theorem mgfE_vp :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem)
      (.block updCtrArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) := by
  have hg := P.hg
  refine VP.taint [.esp, .ebp] updCtrArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hm, rp⟩, cb⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_slot hg (by decide) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => ?_
  refine wp_mov fun t5 u5 => wp_addi fun t6 u6 => wp_movi fun t7 u7 => WP.block_nil ?_
  have c7 : Ctx L scr σ t7 := (((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
    (by decide) (by decide)).upd u7 (by decide) (by decide)
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨c7, m7 ▸ hm, m7 ▸ rp, by rw [List.nil_append, P.sd σ],
    by rw [m7]; exact bytesAt_scr hg (by oomega) (by decide) (i2osp4_length c) cb, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      u2.mem, u1.mem, P.srcL σ _ hm.1]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr]; rfl
  · simp (disch := decide) only [u7.other, u6.gpr, u5.gpr, u4.other, u3.other, u2.other, u1.other, hc.ebp]
  · rw [u7.gpr]

/-- `update` absorbs the counter. -/
theorem mgfF_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
      (hUpd g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aC : (scr + BitVec.ofNat 32 oCtr).setWidth 64 = sa scr oCtr := hg.scrA (by oomega)
  refine upd_vp hg g.H g.ok (msg := fun σ => [] ++ seed σ) (dat := fun _ => Spec.Rsa.i2osp c 4) (c := sl)
    (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv) (hg.rbuf (o := oCtr) (n := 4) (by oomega) (by decide))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aC]; exact hg.low ok (by oomega))
    (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low

/-- `update` absorbs the counter, through the table. -/
theorem mgfF_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) ∧ s.syms = σ.syms)
      (callUpd f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
      Spec.Sha256.bytesAt s.mem ((scr + BitVec.ofNat 32 oCtr).setWidth 64) 4 = Spec.Rsa.i2osp c 4 ∧
      UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
    (fun _ _ _ _ ⟨r, l, b, ua⟩ u => ⟨u.mem ▸ r, l, u.mem ▸ b, ua.esi u⟩) (k := 1) (by decide) P.fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩) (VP.syms (mgfF_call P c))

/-- `finalize(state, sl + 4, scratch + oDig)`'s arguments. -/
theorem mgfG_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4))
      (.block finArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) := by
  have hg := P.hg
  refine VP.taint [.esp, .ebp] finArgs_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, rp⟩ => ?_
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_slot hg (by decide) (by decide) (by decide) fun t3 c3 u3 => wp_addi fun t4 u4 => wp_movi fun t5 u5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => WP.block_nil ?_
  have c7 : Ctx L scr σ t7 := ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6
    (by decide) (by decide)).upd u7 (by decide) (by decide))
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨c7, m7 ▸ hm, m7 ▸ rp, by rw [List.length_append, List.nil_append, P.sd σ, i2osp4_length],
    ⟨?_, ?_, ?_, ?_⟩⟩
  · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.mem, u1.mem,
      P.srcL σ _ hm.1, BitVec.ofNat_add_ofNat]
  · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr]; rfl
  · simp (disch := decide) only [u7.gpr, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other, hc.ebp]

/-- `finalize` writes the digest. -/
theorem mgfH_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
      (hFin g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le; have := g.F_le; have := g.DF
  refine (fin_vp hg g.H g.ok (o := oDig) (c := sl + 4) (msg := fun σ => [] ++ seed σ ++ Spec.Rsa.i2osp c 4)
    (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv)
    (.inr (by oomega)) (by oomega) (by oomega) (by oomega) fun σ m m' hm hf =>
      P.keep hm hf (fun r hr => ?_) fun r hr => ?_).mono
    (fun _ _ h => h) fun σ s ⟨hc, hm, hd⟩ => ⟨hc, hm, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_lo (by oomega)
    · exact P.away_low
  · have e := congrArg (fun l => l.getD i 0) hd
    simp only [List.nil_append] at e
    rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, Spec.Sha256.bytesAt,
      List.getElem?_map, List.getElem?_range (by omega_arith)]
    simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `finalize` writes the digest, through the table. -/
theorem mgfH_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) ∧ s.syms = σ.syms)
      (callFin f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
      ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
    (fun _ _ _ _ ⟨r, l, fa⟩ u => ⟨u.mem ▸ r, l, fa.esi u⟩) (k := 2) (by decide) P.fne.2.2 (a := af)
    (fun σ T => ⟨T.mem.2.2.trans T.af, T.af, T.ok.f⟩) (VP.syms (mgfH_call P c))

/-- The XOR's registers. -/
theorem mgfI_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem)
      (.block xorSet)
      (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] xorSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hm, hd⟩ => ?_
  simp only [xorSet, Impl.RsaPss.X86.atS, Impl.RsaPss.X86.addSlot, Impl.RsaPss.X86.ld,
    Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  have rS : ∀ {t : State} (d : Nat), Ctx L scr σ t → d + 4 ≤ frameBytes →
      InRegions (t.rd ++ t.wr) (VG.X86.addr L.B d) 4 := fun d ct hd => by
    rw [hg.aFr ok d hd]; exact ct.rFr hg d hd
  have hD8 : ∀ t : State, t.mem = s.mem → t.mem.readW (VG.X86.addr L.B sHl) 32 = BitVec.ofNat 32 g.H.D :=
    fun t ht => by rw [ht, hg.aFr ok sHl (by decide)]; exact hm.2.hlS
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_addm (B := L.B) (by rw [c1.st.sp]) (rS sDone c1 (by decide)) fun t2 u2 => ?_
  have c2 : Ctx L scr σ t2 := c1.upd u2 (by decide) (by decide)
  refine wp_mov fun t3 u3 => wp_addi fun t4 u4 => ?_
  have c4 : Ctx L scr σ t4 := (c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_subm (B := L.B) (by rw [c5.st.sp]) (rS sDone c5 (by decide)) fun t6 u6 => ?_
  have c6 : Ctx L scr σ t6 := c5.upd u6 (by decide) (by decide)
  refine wp_mov fun t7 u7 => ?_
  have c7 : Ctx L scr σ t7 := c6.upd u7 (by decide) (by decide)
  have m5 : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have m7 : t7.mem = s.mem := by rw [u7.mem, u6.mem, m5]
  refine wp_subm_cf (B := L.B) (by rw [c7.st.sp]) (rS sHl c7 (by decide)) fun t8 u8 c8 => ?_
  rw [hD8 t7 m7] at c8
  refine wp_sbb_self c8 fun t9 u9 => wp_and fun t10 u10 => ?_
  have c10 : Ctx L scr σ t10 := ((c7.upd u8 (by decide) (by decide)).upd u9 (by decide) (by decide)).upd u10
    (by decide) (by decide)
  have m10 : t10.mem = s.mem := by rw [u10.mem, u9.mem, u8.mem, m7]
  refine wp_addm (B := L.B) (by rw [c10.st.sp]) (rS sHl c10 (by decide)) fun t11 u11 => wp_mov fun t12 u12 =>
    WP.block_nil ?_
  have m12 : t12.mem = s.mem := by rw [u12.mem, u11.mem, m10]
  have hx : dl - c * g.H.D < 2 ^ 32 := by oomega
  have e6 : t6.gpr .ecx = BitVec.ofNat 32 (dl - c * g.H.D) := by
    rw [u6.gpr, u5.gpr, m5, u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sDone (by decide),
      P.dstL σ _ hm.1, hm.2.done, sub_ofNat (by omega_arith)]
  refine ⟨(c10.upd u11 (by decide) (by decide)).upd u12 (by decide) (by decide), by rw [m12]; exact ⟨hm, hd⟩,
    ?_, ?_, ?_⟩
  · simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.gpr, u1.gpr, u1.mem, hg.aFr ok sDone (by decide), P.dst σ _ hm.1,
      hm.2.done, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.gpr, u3.gpr, u2.other, u1.other, hc.ebp]
  · rw [u12.gpr, u11.gpr, hD8 t10 m10, u10.gpr, u9.gpr, u9.other .eax (by decide), u8.gpr, hD8 t7 m7, u7.gpr, e6,
      minSel hx (by omega_arith)]

/-- The XOR of the digest into `dst`. -/
theorem mgfJ_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .edi = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .esi = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .ecx = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D)))
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) s.mem) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have := P.do0; have := P.so0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hn : min g.H.D (dl - c * g.H.D) = n
  have hn0 : 0 < n := by omega_arith
  have hnD : n ≤ g.H.D := by omega_arith
  have hnd : c * g.H.D + n ≤ dl := by omega_arith
  refine (xor_vp hg (od := dOff + c * g.H.D) (os := oDig) (n := n) hn0 (by oomega) (by oomega) (by oomega)
    (X := fun σ m => MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m ∧ Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) m)).mono
    (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨hm, hd⟩, hf, hx⟩ => ⟨hc, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · refine P.I σ _ _ hm.1 (Frame.sub hf fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sR scr dOff dl, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.tabS
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.hlS
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.ctr
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.done
  · have old := hm.2.dx i hi
    by_cases h1 : i < c * g.H.D
    · rw [ite_eq_left (by omega_arith)]
      rw [ite_eq_left h1] at old
      rw [← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    rw [ite_eq_right h1] at old
    by_cases h2 : i < c * g.H.D + n
    · rw [ite_eq_left (by omega_arith), g.mask_byte (c := c) hi (by omega_arith) (by omega_arith), ← hd _ (by omega_arith), ← old]
      have e := hx (i - c * g.H.D) (by omega_arith)
      rw [show dOff + c * g.H.D + (i - c * g.H.D) = dOff + i by omega_arith] at e
      exact e
    · rw [ite_eq_right (by omega_arith), ← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases P.sep with h | h
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)) (by oomega) hm.2.sd

/-- The next counter and bytes masked. -/
theorem mgfK_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) s.mem)
      (.block mgfNext)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.cf = some (decide (c * g.H.D + g.H.D < dl))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hfs := P.fs
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] mgfNext_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hm⟩ => ?_
  simp only [mgfNext, Impl.RsaPss.X86.ld, Impl.RsaPss.X86.st, Impl.RsaPss.X86.addi, Impl.RsaPkcs1Sig.X86.stk]
  refine hc.wp_slot hg (by decide) (by decide) (by decide) fun t1 c1 u1 => wp_addi fun t2 u2 => ?_
  refine (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 => ?_
  refine c3.wp_slot hg (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_addm (B := L.B) (by rw [c4.st.sp]) (by rw [hg.aFr ok sHl (by decide)]; exact c4.rFr hg sHl (by decide))
    fun t5 u5 => ?_
  refine (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 u6 => ?_
  refine wp_cmpm (B := L.B) (by rw [c6.st.sp]) (by rw [hg.aFr ok sDstLen (by decide)]; exact c6.rFr hg sDstLen (by decide))
    fun t7 u7 cf _ => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (c + 1) := by rw [u2.gpr, u1.gpr, hm.ctr, BitVec.ofNat_add_ofNat]
  have m3 : t3.mem = s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1)) := by rw [u3.mem, e2, u2.mem, u1.mem]
  have e5 : t5.gpr .eax = BitVec.ofNat 32 (c * g.H.D + g.H.D) := by
    rw [u5.gpr, u4.gpr, u4.mem, m3, hg.aFr ok sHl (by decide),
      Lay.readW_fr_other (d := sDone) (e := sCtr) L _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sHl) (e := sCtr) L _ _ (by decide) (by decide) (by decide), hm.done, hm.hlS,
      BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
      (BitVec.ofNat 32 (c * g.H.D + g.H.D)) := by rw [u7.mem, u6.mem, e5, u5.mem, u4.mem, m3]
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  rw [u6.gpr, e5, u6.mem, e5, u5.mem, u4.mem, m3, hg.aFr ok sDstLen (by decide),
    Lay.readW_fr_other (d := sDstLen) (e := sDone) L _ _ (by decide) (by decide) (by decide),
    Lay.readW_fr_other (d := sDstLen) (e := sCtr) L _ _ (by decide) (by decide) (by decide), P.dstL σ _ hi,
    toNat_ofNat_lt (by oomega), toNat_ofNat_lt (by oomega)] at cf
  refine ⟨c6.fupd u7, ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, cf⟩
  · rw [m7, Lay.readW_fr_other (d := sTab) (e := sDone) L _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sTab) (e := sCtr) L _ _ (by decide) (by decide) (by decide), hm.tabS]
  · rw [m7, Lay.readW_fr_other (d := sHl) (e := sDone) L _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sHl) (e := sCtr) L _ _ (by decide) (by decide) (by decide), hm.hlS]
  · rw [m7, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m7, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.dx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
      (mgfRound f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.cf = some (decide (c * g.H.D + g.H.D < dl))) ∧ s.syms = σ.syms) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fd
    have : c ≤ c * g.H.D := Nat.le_mul_of_pos_right c g.D_pos
    oomega
  show VP _ (.seq (.block initArgs) (.seq (callInit f) (.seq (.block updSrcArgs) (.seq (callUpd f)
    (.seq (.block ctrSet) (.seq (.block updCtrArgs) (.seq (callUpd f) (.seq (.block finArgs)
      (.seq (callFin f) (.seq (.block xorSet) (.seq (countLoop xorBody)
        (.block mgfNext)))))))))))) _
  exact vpAssoc (VP.seq (mgfA_vp P c) (VP.seq (VP.syms (mgfB_vp P c)) (VP.seq (mgfC_vp P c)
    (VP.seq (VP.syms (mgfD_vp P c hc32)) (VP.seq (VP.syms (mgfE_vp P c)) (VP.seq (mgfF_vp P c)
      (VP.seq (VP.syms (mgfG_vp P c)) (VP.seq (mgfH_vp P c) (VP.seq (VP.syms (mgfI_vp P c hcd))
        (VP.seq (VP.syms (mgfJ_vp P c hcd)) (VP.syms (mgfK_vp P c hcd))))))))))))

end Iter

/-- `dst ⊕= MGF1(src, dl)`. -/
theorem mgf_vp (P : MP g L scr so sl dOff dl seed Inv f j ai au af) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧ s.syms = σ.syms)
      (mgfXor f j)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i ^^^ (Spec.Mgf1.mgf1 g.G (seed σ) dl).getD i 0) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧ s.syms = σ.syms) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have hdl := P.dl0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hK : (dl + g.H.D - 1) / g.H.D = K
  have hK0 : 0 < K := by
    rw [← hK]; exact (Nat.le_div_iff_mul_le hD0).2 (by omega_arith)
  have dis : ∀ d, d + 4 ≤ frameBytes → ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint (slotR L d) :=
    fun d hd o n hon => (hg.slot ok hon (by rw [hg.F]; omega_arith)).symm
  -- The table's address to its slot, then its digest length, the counter and `done` set to 0.
  let p := L.argv.getD j 0
  show VP _ (.seq (.block ([Impl.RsaPss.X86.ld .eax (Impl.RsaPss.X86.arg j), Impl.RsaPss.X86.st .eax sTab] ++
    ([.mov .eax (.mem (Impl.RsaPkcs1Sig.X86.at_ .eax 16)), Impl.RsaPss.X86.st .eax sHl] ++
      Impl.RsaPss.X86.mgfInit))) (.loop (mgfRound f) .b)) _
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl 0 dstv seed Inv σ s.mem) ∧
    s.syms = σ.syms) (VP.block_append (G := fun σ s => ((Ctx L scr σ s ∧ Inv σ s.mem ∧
      (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i) ∧ ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧
      s.syms = σ.syms) ∧ s.mem.readW (L.fr sTab) 32 = p ∧ s.gpr .eax = p)
    (VP.taint [.esp, .ebp] P.cA (sp_bp fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hd, hs⟩, sy⟩ => ?_)
    (VP.taint [.esp, .ebp, .eax] tabHead_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨⟨⟨hc, hi, hd, hs⟩, sy⟩, ht, he⟩ => ?_)) ?_
  · simp only [Impl.RsaPss.X86.ld, Impl.RsaPss.X86.st, Impl.RsaPss.X86.arg, Impl.RsaPkcs1Sig.X86.stk]
    refine hc.wp_arg hg P.hj (by decide) (by decide) fun t1 c1 u1 => c1.wp_st hg (by decide) fun t2 c2 u2 =>
      WP.block_nil ?_
    have fr : Frame [slotR L sTab] s.mem t2.mem := by rw [u2.mem, u1.mem]; exact slot_frame L _ _ _
    refine ⟨⟨⟨c2, P.I σ _ _ hi (fr.mono (by simp)), fun i hi' => ?_, ?_⟩, u2.syms.trans (u1.syms.trans sy)⟩, ?_, ?_⟩
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hs
    · rw [u2.mem, Mem.readW_writeW_self32, u1.gpr]
    · rw [u2.gpr, u1.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.1.st.sp, h₂.1.1.1.st.sp]
    · rw [h₁.1.1.1.ebp, h₂.1.1.1.ebp]
    · rw [h₁.2.2, h₂.2.2]
  · have T := P.tab σ _ hi
    obtain ⟨tR, tRo, tC⟩ := P.tbl
    simp only [Impl.RsaPss.X86.st, Impl.RsaPss.X86.mgfInit, Impl.RsaPss.X86.mi, Impl.RsaPkcs1Sig.X86.at_,
      Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_ldm (B := p) he ⟨tR, hc.st.inRo tRo, tC 16 (by decide)⟩ fun t1 u1 => ?_
    have c1 : Ctx L scr σ t1 := hc.upd u1 (by decide) (by decide)
    refine c1.wp_st hg (by decide) fun t2 c2 u2 => wp_movi fun t3 u3 => ?_
    refine (c2.upd u3 (by decide) (by decide)).wp_st hg (by decide) fun t4 c4 u4 =>
      c4.wp_st hg (by decide) fun t5 c5 u5 => WP.block_nil ?_
    have eD : t1.gpr .eax = BitVec.ofNat 32 g.H.D := by
      rw [u1.gpr, St_roW hc.st tRo (tC 16 (by decide)), T.d]
    have m5 : t5.mem = ((s.mem.writeW (L.fr sHl) (BitVec.ofNat 32 g.H.D)).writeW (L.fr sCtr) (0 : BitVec 32)).writeW
        (L.fr sDone) (0 : BitVec 32) := by
      rw [u5.mem, u4.gpr, u4.mem, u3.gpr, u3.mem, u2.mem, u1.mem, eD]; rfl
    have fr : Frame [slotR L sHl, slotR L sCtr, slotR L sDone] s.mem t5.mem := by
      rw [m5]
      exact (((slot_frame L _ _ _).mono (by simp)).trans ((slot_frame L _ _ _).mono (by simp))).trans
        ((slot_frame L _ _ _).mono (by simp))
    have dis3 : ∀ r ∈ [slotR L sHl, slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact dis _ (by decide) _ _ hon
    refine ⟨⟨c5, P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_, fun i hi' => ?_, ?_⟩⟩,
      u5.syms.trans (u4.syms.trans (u3.syms.trans (u2.syms.trans (u1.syms.trans sy))))⟩
    · rw [m5, Lay.readW_fr_other (d := sTab) (e := sDone) L _ _ (by decide) (by decide) (by decide),
        Lay.readW_fr_other (d := sTab) (e := sCtr) L _ _ (by decide) (by decide) (by decide),
        Lay.readW_fr_other (d := sTab) (e := sHl) L _ _ (by decide) (by decide) (by decide), ht]
    · rw [m5, Lay.readW_fr_other (d := sHl) (e := sDone) L _ _ (by decide) (by decide) (by decide),
        Lay.readW_fr_other (d := sHl) (e := sCtr) L _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [m5, Lay.readW_fr_other (d := sCtr) (e := sDone) L _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]; rfl
    · rw [m5, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
    · rw [ite_eq_right (by omega_arith)]
      exact sbytes_keep fr (fun r hr => dis3 r hr _ _ (by oomega)) (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => dis3 r hr _ _ (by oomega)) (by oomega) hs
  refine (VP.loop (I := fun k σ s => k ≤ K ∧ (Ctx L scr σ s ∧
      MI g (j := j) L scr so sl dOff dl (K - k) dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
    (fun k => ?_) (K - 1)).mono (fun σ s hs => ⟨by omega_arith, by rw [show K - (K - 1 + 1) = 0 by omega_arith]; exact hs⟩)
    fun _ _ h => h
  by_cases hk : k + 1 ≤ K
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hk h
  generalize hc : K - (k + 1) = c
  have key : ∀ x, (dl + g.H.D - 1) / g.H.D ≤ x + 1 ↔ dl ≤ x * g.H.D + g.H.D := fun x => by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hD0, Nat.succ_mul, Nat.succ_mul]
    omega_arith
  have hcd : c * g.H.D < dl := by
    have := (Nat.le_div_iff_mul_le hD0).1 (show c + 1 ≤ (dl + g.H.D - 1) / g.H.D by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  refine (mgfIter_vp P c hcd).mono (fun σ s ⟨_, hs⟩ => hs) fun σ s ⟨⟨hc', hm, z⟩, sy⟩ =>
    ⟨?_, fun h0 => ?_, fun hp => ?_⟩
  · show eval .b s = _
    simp only [eval, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_false (fun h' => by have := e.2 (by omega_arith); omega_arith), hz]; rfl
    · rw [decide_eq_true (by by_contra h'; have := e.2 (by omega_arith); omega_arith), decide_eq_true (by omega_arith)]
  · have e := (key c).1 (by omega_arith)
    refine ⟨⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩, sy⟩
    rw [hm.2.dx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega_arith)]
  · exact ⟨by omega_arith, ⟨hc', by rw [show K - k = c + 1 by omega_arith]; exact hm⟩, sy⟩

end VG.Proof.RsaOaep.X86
