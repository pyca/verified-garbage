module

public import VerifiedGarbage.Impl.Aes.X86.Chain
public import VerifiedGarbage.Proof.Aes.X86.Vperm
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-!
# AES, one block after another, with the keys set up once (x86, 32-bit)

What an implementation of AES for a chain of blocks (`Impl/Aes/X86/Chain.lean`)
must do (`ChainOk`), that the two of them do it (`aesNi_ok`, `ssse3_ok`), and
the chain of blocks around any of them (`mid_wp`): an invariant of the block
number, the chaining value and the memory, which the mode gives, holds after
each block if it is kept by a block's step.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Chain

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86 (Chain)
open VG.Impl.Aes.X86.AesNi (at_ argOp)
open VG.Proof.Aes.X86 (reg32 addr_zero addr_add in_rd part_sub_reg)
open VG.Proof.Aes.X86.AesNi (st st_toList XFrame Keys aes_ok byte_roundKey ofInt_natCast)
open VG.Spec.Aes (bytesAt cipher)

/-- The arguments of a chain's `prep`: the schedule at `S`, for `R` rounds, and
the scratch buffer at `B`. -/
structure Keyed (S : BitVec 32) (R : Nat) (B : BitVec 32) (s : State) : Prop where
  a0 : arg s 0 = S
  a1 : arg s 1 = BitVec.ofNat 32 R
  a5 : arg s 5 = B
  argIn : ∀ i < 6, InRegions (s.rd ++ s.wr) (argAddr s i) 4
  argScr : ∀ i < 6, Region.Disjoint ⟨argAddr s i, 4⟩ (reg32 B 2176)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  schFit : S.toNat + 240 ≤ 2 ^ 32
  sch : reg32 S 240 ∈ s.rd ++ s.wr
  schScr : (reg32 S 240).Disjoint (reg32 B 2176)
  scrFit : B.toNat + 2176 ≤ 2 ^ 32
  scr : reg32 B 2176 ∈ s.wr

/-- The round keys' bytes. -/
abbrev sched (S : BitVec 32) (R : Nat) (m : Mem) : List Byte := bytesAt m (S.setWidth 64) (16 * (R + 1))

/-- What a mode keeps between two runs of a chain's `core`. -/
structure Same (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .edx → s'.gpr r = s.gpr r
  xmm : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → s'.xmm r = s.xmm r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What `core` keeps, and its result. -/
structure CoreOut (w : Nat) (B : BitVec 32) (s s' : State) : Prop where
  esi : s'.gpr .esi = s.gpr .esi
  ebp : s'.gpr .ebp = s.gpr .ebp
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [reg32 B w] s.mem s'.mem

/-- An implementation of AES for a chain of blocks. -/
structure ChainOk (c : Chain) : Prop where
  le : c.written ≤ 2048
  ok : ∀ {S : BitVec 32} {R : Nat} {B : BitVec 32} {s₀ : State}, Keyed S R B s₀ → ∃ Ready : State → Prop,
    WP isa c.prep s₀ (fun s => Ready s ∧ s.gpr .esp = s₀.gpr .esp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      Frame [reg32 B c.written] s₀.mem s.mem) ∧
    (∀ {s : State}, Ready s → WP isa c.core s fun s' => Ready s' ∧
      st (s'.xmm .xmm0) = cipher R (sched S R s₀.mem) (st (s.xmm .xmm0)) ∧ CoreOut c.written B s s') ∧
    ∀ {s s' : State} {rs : List Region}, Ready s → Same s s' → Frame rs s.mem s'.mem →
      (∀ r ∈ rs, (reg32 B c.written).Disjoint r ∧ (reg32 S 240).Disjoint r ∧
        ∀ i < 2, Region.Disjoint ⟨argAddr s₀ i, 4⟩ r) → Ready s'

/-! ## AES-NI -/

theorem Keyed.le {S : BitVec 32} {R : Nat} {B : BitVec 32} {s : State} (h : Keyed S R B s) : R ≤ 14 := by
  rcases h.rounds with h | h | h <;> omega_using [h]

/-- The round keys, read from the schedule that `eax` points at. -/
theorem niKeys {s : State} {P : BitVec 32} {nr : Nat} (hnr : nr ≤ 14) (hfit : P.toNat + 240 ≤ 2 ^ 32)
    (heax : s.gpr .eax = P) (hmem : reg32 P 240 ∈ s.rd ++ s.wr) :
    Keys nr (bytesAt s.mem (P.setWidth 64) (16 * (nr + 1))) s := by
  obtain he : ∀ j ≤ nr, s.ea (at_ .eax (16 * j)) = P.setWidth 64 + BitVec.ofNat 64 (16 * j) := fun j hj => by
    show addr (s.gpr .eax) (16 * j) = _
    rw [heax]
    exact addr_eq (by omega_using [hfit, hj, hnr])
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj]
    exact ⟨_, hmem, Offset.contains_base _ (by omega_using [hj, hnr]) (by omega_using [hj, hnr])⟩
  · rw [he j hj]
    have h := byte_roundKey s.mem (P.setWidth 64) (L := 16 * (nr + 1)) (j := j) (by omega_using [hj])
    rw [ofInt_natCast] at h
    exact h

theorem sched_frame {S : BitVec 32} {R : Nat} (hR : R ≤ 14) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (reg32 S 240).Disjoint r) : sched S R m' = sched S R m :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_using [hR])))
    (by omega_using [hR])

theorem aesNi_ok : ChainOk Chain.aesNi where
  le := by decide
  ok := fun {S R B s₀} hk => by
    refine ⟨fun s => s.gpr .eax = S ∧ s.gpr .ecx = BitVec.ofNat 32 R ∧ reg32 S 240 ∈ s.rd ++ s.wr ∧
      sched S R s.mem = sched S R s₀.mem, ?_, fun {s} ⟨ha, hc, hs, hw⟩ => ?_, fun {s s' rs} ⟨ha, hc, hs, hw⟩ h hf hd => ?_⟩
    · refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 0) rfl (hk.argIn 0 (by decide)) fun s₁ u₁ => ?_
      refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 1) (u₁.other _ (by decide))
        (by rw [u₁.rd, u₁.wr]; exact hk.argIn 1 (by decide)) fun s₂ u₂ => WP.block_nil ?_
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [u₂.other _ (by decide), u₁.gpr]; exact hk.a0
      · rw [u₂.gpr, u₁.mem]; exact hk.a1
      · rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hk.sch
      · rw [u₂.mem, u₁.mem]
      · rw [u₂.other _ (by decide), u₁.other _ (by decide)]
      · rw [u₂.rd, u₁.rd]
      · rw [u₂.wr, u₁.wr]
      · rw [u₂.mem, u₁.mem]; exact Frame.refl _ _
    · have hK : Keys R (sched S R s.mem) s := niKeys hk.le hk.schFit ha hs
      rw [hw] at hK
      refine WP.mono (aes_ok [.xmm0] (by decide) (by decide) hk.rounds s hK hc) fun s' ⟨x, f⟩ =>
        ⟨⟨?_, ?_, ?_, ?_⟩, x _ List.mem_cons_self, ⟨?_, ?_, ?_, f.rd, f.wr, ?_⟩⟩
      · rw [f.gpr]; exact ha
      · rw [f.gpr]; exact hc
      · rw [f.rd, f.wr]; exact hs
      · rw [f.mem]; exact hw
      · rw [f.gpr]
      · rw [f.gpr]
      · rw [f.gpr]
      · rw [f.mem]; exact Frame.refl _ _
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h.gpr _ (by decide) (by decide) (by decide)]; exact ha
      · rw [h.gpr _ (by decide) (by decide) (by decide)]; exact hc
      · rw [h.rd, h.wr]; exact hs
      · rw [sched_frame hk.le hf fun r hr => (hd r hr).2.1]; exact hw

/-! ## SSSE3 -/

open VG.Proof.Aes.X86.Vperm in
theorem ssse3_ok : ChainOk Chain.ssse3 where
  le := by decide
  ok := fun {S R B s₀} hk => by
    have hN : (Impl.Aes.X86.Vperm.Enc.dir false).saved + 16 ≤ 2176 := by decide
    have hs : Sched 2176 B S R (sched S R s₀.mem) s₀ :=
      { fit := hk.schFit
        sch := hk.sch
        sep := hk.schScr
        argIn := fun i hi => hk.argIn i (by omega_using [hi])
        argSep := fun i hi => hk.argScr i (by omega_using [hi])
        arg0 := hk.a0
        arg1 := hk.a1
        rounds := hk.rounds
        key := fun j hj => by
          have hR := hk.le
          rw [addr_eq (by have := hk.schFit; omega_using [hj, hR, this])]
          exact VG.Proof.Aes.Vector.keyIs_readW _ _ (by omega_using [hj]) }
    obtain ⟨sk, hprep, hcore⟩ := (Enc.cryptOk (b := false)).prep hk.scrFit hN hk.scr hs
    refine ⟨fun s => CoreIn (Impl.Aes.X86.Vperm.Enc.dir false) Enc.all 2176 B R sk s ∧ s.gpr .esp = s₀.gpr .esp, ?_,
      fun {s} ⟨hc, hp⟩ => ?_, fun {s s' rs} ⟨hc, hp⟩ h hf hd => ?_⟩
    · refine WP.seq (WP.mono (setup_ok (Enc.setupOk (b := false)) (k := 5) (N := 2176) (B := B)
        ⟨hk.scrFit, hk.scr, hk.argIn 5 (by decide), hk.a5⟩ hN) fun s₁ ⟨h₁, h6, h7⟩ => ?_)
      exact WP.mono (hprep h₁ h6 h7) fun s₂ ⟨h₂, c₂⟩ => ⟨⟨c₂, h₂.esp⟩, h₂.esp, h₂.rd, h₂.wr, h₂.frame⟩
    · refine WP.mono (hcore hc) fun s' ⟨k, x⟩ => ⟨⟨hc.of_kept k, ?_⟩, x, ⟨?_, ?_, ?_, k.rd, k.wr, ?_⟩⟩
      · rw [k.gpr _ (by decide) (by decide)]; exact hp
      · exact k.gpr _ (by decide) (by decide)
      · exact k.gpr _ (by decide) (by decide)
      · exact k.gpr _ (by decide) (by decide)
      · rw [k.mem]; exact Frame.refl _ _
    · have e := h.gpr .esp (by decide) (by decide) (by decide)
      refine ⟨hc.of_frame (h.gpr _ (by decide) (by decide) (by decide)) e h.rd h.wr
        (h.xmm _ (by decide) (by decide)) (h.xmm _ (by decide) (by decide)) hf rfl (fun o ho r hr => ?_) (fun r hr => ?_),
        e.trans hp⟩
      · have ho' : o + 16 ≤ 480 := Nat.le_trans ho (by decide)
        exact (hd r hr).1.sub_left (part_sub_reg (N := 480) (by have := hk.scrFit; omega_using [this]) ho')
      · rw [hp]; exact (hd r hr).2.2 1 (by decide)

/-- Each of them. -/
theorem of_ok {name : String} {c : Chain} (h : Chain.of name = some c) : ChainOk c := by
  unfold Chain.of at h
  split at h
  · exact Option.some.inj h ▸ aesNi_ok
  · split at h
    · exact Option.some.inj h ▸ ssse3_ok
    · exact absurd h (fun h => nomatch h)

theorem of_cases {name : String} {c : Chain} (h : Chain.of name = some c) : c = Chain.aesNi ∨ c = Chain.ssse3 := by
  unfold Chain.of at h
  split at h
  · exact .inl (Option.some.inj h).symm
  · split at h
    · exact .inr (Option.some.inj h).symm
    · exact absurd h (fun h => nomatch h)

theorem choose_some {name : String} {c : Chain} (h : Chain.of name = some c) (f : Chain → Prog isa) (d : Prog isa) :
    Chain.choose name f d = f c := by
  unfold Chain.of at h
  unfold Chain.choose
  split at h
  · next hn => rw [ite_eq_left hn, Option.some.inj h]
  · next hn =>
    rw [ite_eq_right hn]
    split at h
    · next hs => rw [ite_eq_left hs, Option.some.inj h]
    · exact absurd h (fun h => nomatch h)

theorem choose_none {name : String} (h : Chain.of name = none) (f : Chain → Prog isa) (d : Prog isa) :
    Chain.choose name f d = d := by
  unfold Chain.of at h
  unfold Chain.choose
  split at h
  · exact absurd h (fun h => nomatch h)
  · next hn =>
    rw [ite_eq_right hn]
    split at h
    · exact absurd h (fun h => nomatch h)
    · next hs => rw [ite_eq_right hs]

/-- The code a mode chooses. -/
theorem choose_cases (name : String) (f : Chain → Prog isa) (d : Prog isa) :
    (∃ c, Chain.of name = some c ∧ Chain.choose name f d = f c) ∨ Chain.choose name f d = d := by
  cases h : Chain.of name with
  | some c => exact .inl ⟨c, rfl, choose_some h f d⟩
  | none => exact .inr (choose_none h f d)

/-! ## What the modes do with a block -/

/-- The block written over, if it is. -/
def upd (w : Option (BitVec 128 → BitVec 128 → BitVec 128)) (m : Mem) (a : Addr) (e d : BitVec 128) : Mem :=
  match w with
  | none => m
  | some w => m.writeW a (w e d)

/-- The mode `m` enciphers `f x d` for the chaining value `x` and the block
`d`, and of the result `e` makes the chaining value `g e d` and, if `w` is
some, the block `w e d`. -/
structure ModeOk (m : Chain.Mode) (f g : BitVec 128 → BitVec 128 → BitVec 128)
    (w : Option (BitVec 128 → BitVec 128 → BitVec 128)) : Prop where
  pre : ∀ {s : State} {a : Addr}, s.ea (at_ .esi 0) = a → InRegions (s.rd ++ s.wr) a 16 →
    WP isa (.block m.pre) s fun s' => s'.xmm .xmm0 = f (s.xmm .xmm0) (s.mem.readW a 128) ∧
      XFrame [.xmm0, .xmm1] s s'
  post : ∀ {s : State} {a : Addr}, s.ea (at_ .esi 0) = a → InRegions (s.rd ++ s.wr) a 16 →
    (w.isSome = true → InRegions s.wr a 16) →
    WP isa (.block m.post) s fun s' => s'.xmm .xmm0 = g (s.xmm .xmm0) (s.mem.readW a 128) ∧
      s'.mem = upd w s.mem a (s.xmm .xmm0) (s.mem.readW a 128) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → s'.xmm r = s.xmm r

abbrev pxor (a b : BitVec 128) : BitVec 128 := XBinOp.eval .pxor a b

/-- The block XORed into `xmm0`. -/
theorem xorIn_ok {s : State} {a : Addr} {rest : List Instr} {Q : State → Prop} (hea : s.ea (at_ .esi 0) = a)
    (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', s'.xmm .xmm0 = pxor (s.xmm .xmm0) (s.mem.readW a 128) → XFrame [.xmm0, .xmm1] s s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Chain.xorIn ++ rest)) s Q := by
  obtain ⟨d, hd⟩ : ∃ d, s.mem.readW a 128 = d := ⟨_, rfl⟩
  rw [Chain.xorIn, Chain.loadBlock, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm1 d, by
    simp only [isa, reduceExec, State.load128, hea, hin, ite_true, Option.map_some, hd], ?_⟩
  rw [List.cons_append, List.nil_append, WP.block_cons_iff]
  refine ⟨(s.setXmm .xmm1 d).setXmm .xmm0 (pxor ((s.setXmm .xmm1 d).xmm .xmm0) ((s.setXmm .xmm1 d).xmm .xmm1)), rfl,
    k _ ?_ ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩⟩
  · rw [xmm_setXmm_self, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide), hd]
  · rw [gpr_setXmm, gpr_setXmm]
  · rw [mem_setXmm, mem_setXmm]
  · rw [rd_setXmm, rd_setXmm]
  · rw [wr_setXmm, wr_setXmm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [xmm_setXmm_of_ne _ _ hr.1, xmm_setXmm_of_ne _ _ hr.2]

theorem xorIn_ok' {s : State} {a : Addr} (hea : s.ea (at_ .esi 0) = a) (hin : InRegions (s.rd ++ s.wr) a 16) :
    WP isa (.block Chain.xorIn) s fun s' => s'.xmm .xmm0 = pxor (s.xmm .xmm0) (s.mem.readW a 128) ∧
      XFrame [.xmm0, .xmm1] s s' := by
  have h := xorIn_ok (rest := []) (Q := fun s' => s'.xmm .xmm0 = pxor (s.xmm .xmm0) (s.mem.readW a 128) ∧
    XFrame [.xmm0, .xmm1] s s') hea hin fun s' x f => WP.block_nil ⟨x, f⟩
  rwa [List.append_nil] at h

/-- `xmm0`, or another register, stored over the block. -/
theorem storeBlock_ok {s : State} {a : Addr} {r : XReg} {Q : State → Prop} (hea : s.ea (at_ .esi 0) = a)
    (hin : InRegions s.wr a 16)
    (k : ∀ s', s'.mem = s.mem.writeW a (s.xmm r) → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      Q s') :
    WP isa (.block [.movdquStore (at_ .esi 0) r]) s Q := by
  rw [WP.block_cons_iff]
  exact ⟨{ s with mem := s.mem.writeW a (s.xmm r) }, by
    simp only [isa, reduceExec, State.store128, hea, hin, ite_true], WP.block_nil (k _ rfl rfl rfl rfl rfl)⟩

theorem ea_eq {s s' : State} (h : s'.gpr = s.gpr) (o : MemOp) : s'.ea o = s.ea o := by
  simp only [State.ea, h]

theorem cbc_ok : ModeOk Chain.cbc pxor (fun e _ => e) (some fun e _ => e) where
  pre := fun hea hin => xorIn_ok' hea hin
  post := fun hea _ hw => storeBlock_ok hea (hw rfl) fun s' m g rd wr x =>
    ⟨by rw [x], m, g, rd, wr, fun _ _ _ => by rw [x]⟩

theorem cmac_ok : ModeOk Chain.cmac pxor (fun e _ => e) none where
  pre := fun hea hin => xorIn_ok' hea hin
  post := fun _ _ _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem cfb_ok : ModeOk Chain.cfb (fun x _ => x) pxor (some pxor) where
  pre := fun _ _ => WP.block_nil ⟨rfl, XFrame.refl _ _⟩
  post := fun {s a} hea hin hw => xorIn_ok hea hin fun s₁ x₁ f₁ => by
    refine storeBlock_ok (a := a) (by rw [ea_eq f₁.gpr, hea]) (by rw [f₁.wr]; exact hw rfl) fun s' m g rd wr x => ?_
    refine ⟨by rw [x, x₁], by rw [m, x₁, f₁.mem]; rfl, g.trans f₁.gpr, rd.trans f₁.rd, wr.trans f₁.wr, fun r h0 h1 => ?_⟩
    rw [x, f₁.xmm r (by simp [h0, h1])]

theorem ofb_ok : ModeOk Chain.ofb (fun x _ => x) (fun e _ => e) (some fun e d => pxor d e) where
  pre := fun _ _ => WP.block_nil ⟨rfl, XFrame.refl _ _⟩
  post := fun {s a} hea hin hw => by
    obtain ⟨d, hd⟩ : ∃ d, s.mem.readW a 128 = d := ⟨_, rfl⟩
    rw [Chain.ofb, Chain.loadBlock, WP.block_cons_iff]
    refine ⟨s.setXmm .xmm1 d, by
      simp only [isa, reduceExec, State.load128, hea, hin, ite_true, Option.map_some, hd], ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨(s.setXmm .xmm1 d).setXmm .xmm1 (XBinOp.eval .pxor ((s.setXmm .xmm1 d).xmm .xmm1)
      ((s.setXmm .xmm1 d).xmm .xmm0)), rfl, ?_⟩
    generalize hs₂ : (s.setXmm .xmm1 d).setXmm .xmm1 (XBinOp.eval .pxor ((s.setXmm .xmm1 d).xmm .xmm1)
      ((s.setXmm .xmm1 d).xmm .xmm0)) = s₂
    obtain x₁ : s₂.xmm .xmm1 = pxor d (s.xmm .xmm0) := by
      rw [← hs₂, xmm_setXmm_self, xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide)]
    obtain xo : ∀ r, r ≠ .xmm1 → s₂.xmm r = s.xmm r := fun r hr => by
      rw [← hs₂, xmm_setXmm_of_ne _ _ hr, xmm_setXmm_of_ne _ _ hr]
    obtain g₂ : s₂.gpr = s.gpr := by rw [← hs₂, gpr_setXmm, gpr_setXmm]
    obtain m₂ : s₂.mem = s.mem := by rw [← hs₂, mem_setXmm, mem_setXmm]
    obtain rd₂ : s₂.rd = s.rd := by rw [← hs₂, rd_setXmm, rd_setXmm]
    obtain wr₂ : s₂.wr = s.wr := by rw [← hs₂, wr_setXmm, wr_setXmm]
    refine storeBlock_ok (a := a) (by rw [ea_eq g₂, hea]) (by rw [wr₂]; exact hw rfl) fun s' m g rd wr x => ?_
    refine ⟨by rw [x, xo _ (by decide)], by rw [m, x₁, m₂, hd]; rfl, g.trans g₂, rd.trans rd₂, wr.trans wr₂,
      fun r _ h1 => by rw [x, xo r h1]⟩

/-! ## Registers' bytes -/

/-- The 16 bytes a register was loaded from. -/
theorem st_readW (m : Mem) (a : Addr) : (st (m.readW a 128)).toList = bytesAt m a 16 := by
  rw [st_toList]
  exact List.map_congr_left fun i hi => VG.Proof.Gcm.X86.byte_readW m a (List.mem_range.mp hi)

theorem st_getD (a : BitVec 128) {i : Nat} (hi : i < 16) : (st a).toList.getD i 0 = byte a i := by
  rw [st_toList, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ## The chain -/

/-- A mode's arguments, when its registers are saved: the chaining value at
`P`, and `N` blocks of data at `D`. -/
structure Env (S : BitVec 32) (R : Nat) (P D : BitVec 32) (N : Nat) (B : BitVec 32) (s : State) : Prop
    extends Keyed S R B s where
  a2 : arg s 2 = P
  a3 : arg s 3 = D
  a4 : arg s 4 = BitVec.ofNat 32 N
  iv : reg32 P 16 ∈ s.wr
  ivScr : (reg32 P 16).Disjoint (reg32 B 2176)
  datFit : D.toNat + 16 * N ≤ 2 ^ 32
  dat : reg32 D (16 * N) ∈ s.rd ++ s.wr
  datScr : (reg32 D (16 * N)).Disjoint (reg32 B 2176)

/-- And what a mode that writes the data needs. -/
structure Out (S D : BitVec 32) (N : Nat) (s : State) : Prop where
  wr : reg32 D (16 * N) ∈ s.wr
  sch : (reg32 S 240).Disjoint (reg32 D (16 * N))
  args : ∀ i < 6, Region.Disjoint ⟨argAddr s i, 4⟩ (reg32 D (16 * N))

section
variable {c : Chain} {m : Chain.Mode} {f g : BitVec 128 → BitVec 128 → BitVec 128}
  {w : Option (BitVec 128 → BitVec 128 → BitVec 128)} {S : BitVec 32} {R : Nat} {P D : BitVec 32} {N : Nat}
  {B : BitVec 32} {s₀ : State}

/-- Block `k`. -/
abbrev blk (D : BitVec 32) (k : Nat) : Addr := D.setWidth 64 + BitVec.ofNat 64 (16 * k)

/-- What the chain changes before the chaining value is stored. -/
abbrev changed (c : Chain) (w : Option (BitVec 128 → BitVec 128 → BitVec 128)) (B D : BitVec 32) (N : Nat) :
    List Region :=
  reg32 B c.written :: if w.isSome then [reg32 D (16 * N)] else []

theorem written_sub (hc : ChainOk c) : Region.Sub (reg32 B c.written) (reg32 B 2176) :=
  Region.sub_prefix (by have := hc.le; omega_using [this])

theorem changed_cases {r : Region} (h : r ∈ changed c w B D N) :
    r = reg32 B c.written ∨ w.isSome = true ∧ r = reg32 D (16 * N) := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · split at h
    · next hw => exact .inr ⟨hw, by simpa using h⟩
    · exact absurd h List.not_mem_nil

theorem arg_keep (hc : ChainOk c) (he : Env S R P D N B s₀) (ho : w.isSome = true → Out S D N s₀) {m' : Mem}
    (hf : Frame (changed c w B D N) s₀.mem m') {i : Nat} (hi : i < 6) : m'.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rcases changed_cases hr with rfl | ⟨hw, rfl⟩
    · exact (he.argScr i hi).sub_right (written_sub hc)
    · exact (ho hw).args i hi) (by decide)

/-- After `k` blocks. -/
structure Inv (c : Chain) (w : Option (BitVec 128 → BitVec 128 → BitVec 128)) (D : BitVec 32) (N : Nat) (B : BitVec 32)
    (Ready : State → Prop) (I : Nat → BitVec 128 → Mem → Prop) (s₀ : State) (k : Nat) (s : State) : Prop where
  ready : Ready s
  esi : s.gpr .esi = D + BitVec.ofNat 32 (16 * k)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (N - k)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (changed c w B D N) s₀.mem s.mem
  inv : I k (s.xmm .xmm0) s.mem

/-- One block. -/
theorem body_ok (hc : ChainOk c) (hm : ModeOk m f g w) (he : Env S R P D N B s₀) (ho : w.isSome = true → Out S D N s₀)
    {Ready : State → Prop} {I : Nat → BitVec 128 → Mem → Prop}
    (hcore : ∀ {s : State}, Ready s → WP isa c.core s fun s' => Ready s' ∧
      st (s'.xmm .xmm0) = cipher R (sched S R s₀.mem) (st (s.xmm .xmm0)) ∧ CoreOut c.written B s s')
    (hstable : ∀ {s s' : State} {rs : List Region}, Ready s → Same s s' → Frame rs s.mem s'.mem →
      (∀ r ∈ rs, (reg32 B c.written).Disjoint r ∧ (reg32 S 240).Disjoint r ∧
        ∀ i < 2, Region.Disjoint ⟨argAddr s₀ i, 4⟩ r) → Ready s')
    (hframe : ∀ {k : Nat} {x : BitVec 128} {m m' : Mem}, I k x m → Frame [reg32 B c.written] m m' → I k x m')
    (hstep : ∀ {k : Nat} {x e : BitVec 128} {m : Mem}, k < N → I k x m →
      st e = cipher R (sched S R s₀.mem) (st (f x (m.readW (blk D k) 128))) →
      I (k + 1) (g e (m.readW (blk D k) 128)) (upd w m (blk D k) e (m.readW (blk D k) 128)))
    {k : Nat} (hk : k < N) {s : State} (h : Inv c w D N B Ready I s₀ k s) :
    WP isa (c.body m) s fun s' => Inv c w D N B Ready I s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N)) := by
  have hdf := he.datFit
  have cB : (reg32 D (16 * N)).Contains (blk D k) 16 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hdf, hk])
  have sB : Region.Sub ⟨blk D k, 16⟩ (reg32 D (16 * N)) := Offset.sub_base _ (by omega_using [hk])
  have hea : ∀ {t : State}, t.gpr .esi = s.gpr .esi → t.ea (at_ .esi 0) = blk D k := fun {t} ht => by
    show addr (t.gpr .esi) 0 = _
    rw [ht, h.esi, addr_add, Nat.add_zero, addr_eq (by omega_using [hdf, hk])]
  have hin : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → InRegions (t.rd ++ t.wr) (blk D k) 16 := fun hr hw => by
    rw [hr, hw, h.rd, h.wr]; exact ⟨_, he.dat, cB⟩
  refine WP.seq (WP.mono (hm.pre (hea rfl) (hin rfl rfl)) fun s₁ ⟨x₁, f₁⟩ => ?_)
  have r₁ : Ready s₁ := hstable (rs := []) h.ready
    ⟨fun _ _ _ _ => by rw [f₁.gpr], fun r h0 h1 => f₁.xmm r (by simp [h0, h1]), f₁.rd, f₁.wr⟩
    (by rw [f₁.mem]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil)
  refine WP.seq (WP.mono (hcore r₁) fun s₂ ⟨r₂, x₂, o₂⟩ => ?_)
  -- The block is as it was: the cipher writes only in the scratch buffer.
  have f₂ : Frame [reg32 B c.written] s.mem s₂.mem := by rw [← f₁.mem]; exact o₂.frame
  have d₂ : s₂.mem.readW (blk D k) 128 = s.mem.readW (blk D k) 128 :=
    f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (he.datScr.sub_left sB).sub_right (written_sub hc)) (by decide)
  have esi₂ : s₂.gpr .esi = s.gpr .esi := by rw [o₂.esi, f₁.gpr]
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd, f₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr, f₁.wr]
  rw [WP.block_append_iff]
  refine WP.mono (hm.post (hea esi₂) (hin rd₂ wr₂) fun hw => by rw [wr₂, h.wr]; exact ⟨_, (ho hw).wr, cB⟩)
    fun s₃ ⟨x₃, m₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  refine WP.mono (Vperm.wp_g (Q := fun s' => s'.mem = s₃.mem ∧ s'.rd = s₃.rd ∧ s'.wr = s₃.wr ∧
    (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s₃.gpr r) ∧ s'.gpr .esi = s₃.gpr .esi + 16 ∧
    s'.gpr .ebp = s₃.gpr .ebp - 1 ∧ s'.zf = some (s₃.gpr .ebp - 1 == 0)) rfl ?_) fun s' hh => ?_
  · refine Wp.wp_addi fun t₁ u₁ => Wp.wp_subi fun t₂ u₂ _ z => WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₂.mem, u₁.mem]
    · rw [u₂.rd, u₁.rd]
    · rw [u₂.wr, u₁.wr]
    · rw [u₂.other _ h2, u₁.other _ h1]
    · rw [u₂.other _ (by decide), u₁.gpr]
    · rw [u₂.gpr, u₁.other _ (by decide)]
    · rw [z, u₁.other _ (by decide)]
  obtain ⟨⟨m', rd', wr', g', si, bp, z⟩, x'⟩ := hh
  have mem' : s'.mem = upd w s₂.mem (blk D k) (s₂.xmm .xmm0) (s.mem.readW (blk D k) 128) := by rw [m', m₃, d₂]
  have hw : Frame (if w.isSome then [⟨blk D k, 16⟩] else []) s₂.mem s'.mem := by
    rw [mem']
    cases w with
    | none => exact Frame.refl _ _
    | some w => exact (Frame.refl _ _).writeW (r := ⟨blk D k, 16⟩) List.mem_cons_self _ (Region.contains_self _ _)
  have hwc : ∀ {r : Region}, r ∈ (if w.isSome then [⟨blk D k, 16⟩] else [] : List Region) →
      w.isSome = true ∧ r = ⟨blk D k, 16⟩ := fun {r} hr => by
    split at hr
    · next hw => exact ⟨hw, by simpa using hr⟩
    · exact absurd hr List.not_mem_nil
  have ebp' : s₃.gpr .ebp - 1 = BitVec.ofNat 32 (N - (k + 1)) := by
    rw [g₃, o₂.ebp, f₁.gpr, h.ebp, Wp.ofNat_pred (by omega_using [hk])]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hstable r₂ ⟨fun r h1 h2 _ => by rw [g' r h1 h2, g₃], fun r h0 h1 => by rw [x', o₃ r h0 h1],
      by rw [rd', rd₃], by rw [wr', wr₃]⟩ hw fun r hr => ?_
    obtain ⟨hi, rfl⟩ := hwc hr
    exact ⟨(he.datScr.sub_left sB).symm.sub_left (written_sub hc), (ho hi).sch.sub_right sB,
      fun i hi' => ((ho hi).args i (by omega_using [hi'])).sub_right sB⟩
  · rw [si, g₃, esi₂, h.esi, BitVec.add_assoc]
    exact congrArg _ ((BitVec.ofNat_add _ _).symm.trans (congrArg _ (by omega_using [])))
  · rw [bp, ebp']
  · rw [g' _ (by decide) (by decide), g₃, o₂.esp, f₁.gpr, h.esp]
  · rw [rd', rd₃, rd₂, h.rd]
  · rw [wr', wr₃, wr₂, h.wr]
  · refine h.frame.trans ((f₂.mono fun r hr => ?_).trans (hw.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
    · obtain ⟨hi, rfl⟩ := hwc hr
      exact ⟨reg32 D (16 * N), List.mem_cons_of_mem _ (by simp [hi]), sB⟩
  · rw [mem', x', x₃, d₂]
    have hI := hstep (e := s₂.xmm .xmm0) hk (hframe h.inv f₂) (by rw [x₂, x₁, d₂])
    rw [d₂] at hI
    exact hI
  · have hN : N < 2 ^ 32 + 1 := by omega_using [hdf]
    rw [z, ebp', Wp.ofNat_beq_zero (by omega_using [hdf])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using [hk]))

/-- The chain of at least one block: an invariant `I` of the number of blocks,
the chaining value and the memory, which holds at the start, and which a
block's step keeps, holds at the end, where the chaining value is stored. -/
theorem mid_wp (hc : ChainOk c) (hm : ModeOk m f g w) (he : Env S R P D N B s₀) (ho : w.isSome = true → Out S D N s₀)
    (hN : 0 < N) {I : Nat → BitVec 128 → Mem → Prop} (h0 : I 0 (s₀.mem.readW (P.setWidth 64) 128) s₀.mem)
    (hframe : ∀ {k : Nat} {x : BitVec 128} {m m' : Mem}, I k x m → Frame [reg32 B c.written] m m' → I k x m')
    (hstep : ∀ {k : Nat} {x e : BitVec 128} {m : Mem}, k < N → I k x m →
      st e = cipher R (sched S R s₀.mem) (st (f x (m.readW (blk D k) 128))) →
      I (k + 1) (g e (m.readW (blk D k) 128)) (upd w m (blk D k) e (m.readW (blk D k) 128))) :
    WP isa (c.mid m) s₀ fun s => ∃ x m', I N x m' ∧ Frame (changed c w B D N) s₀.mem m' ∧
      s.mem = m'.writeW (P.setWidth 64) x ∧ s.gpr .esi = D + BitVec.ofNat 32 (16 * N) ∧
      s.gpr .esp = s₀.gpr .esp ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨Ready, hprep, hcore, hstable⟩ := hc.ok he.toKeyed
  refine WP.seq (WP.mono hprep fun s₁ ⟨r₁, esp₁, rd₁, wr₁, f₁⟩ => ?_)
  have hin : ∀ {t : State} {i : Nat}, t.rd = s₀.rd → t.wr = s₀.wr → i < 6 →
      InRegions (t.rd ++ t.wr) (argAddr s₀ i) 4 := fun hr hw hi => by rw [hr, hw]; exact he.argIn _ hi
  have fc : Frame (changed c w B D N) s₀.mem s₁.mem := f₁.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have harg : ∀ {i : Nat}, i < 6 → s₁.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun hi => arg_keep hc he ho fc hi
  have hP : s₁.mem.readW (P.setWidth 64) 128 = s₀.mem.readW (P.setWidth 64) 128 :=
    f₁.readW (r := reg32 P 16) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.ivScr.sub_right (written_sub hc)) (by decide)
  have hPin : ∀ {t : State}, t.wr = s₀.wr → InRegions t.wr (P.setWidth 64) 16 := fun hw => by
    rw [hw]; exact ⟨_, he.iv, Region.contains_self _ _⟩
  refine WP.seq (WP.mono (Q := Inv c w D N B Ready I s₀ 0) ?_ fun s₂ h₂ => ?_)
  · rw [show Chain.load = ([.mov .esi (.mem (argOp 3)), .mov .ebp (.mem (argOp 4)), .mov .edx (.mem (argOp 2))] ++
      [.movdquLoad .xmm0 (at_ .edx 0)] : List Instr) from rfl, WP.block_append_iff]
    refine WP.mono (Vperm.wp_g (Q := fun s' => s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .edx → s'.gpr r = s₁.gpr r) ∧ s'.gpr .esi = D ∧
      s'.gpr .ebp = BitVec.ofNat 32 N ∧ s'.gpr .edx = P) rfl ?_) fun s' hh => ?_
    · refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 3) esp₁ (hin rd₁ wr₁ (by decide)) fun t₁ u₁ => ?_
      refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 4) ((u₁.other _ (by decide)).trans esp₁)
        (hin (u₁.rd.trans rd₁) (u₁.wr.trans wr₁) (by decide)) fun t₂ u₂ => ?_
      refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 2) ((u₂.other _ (by decide)).trans
        ((u₁.other _ (by decide)).trans esp₁)) (hin (u₂.rd.trans (u₁.rd.trans rd₁)) (u₂.wr.trans (u₁.wr.trans wr₁))
        (by decide)) fun t₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
      · rw [u₃.mem, u₂.mem, u₁.mem]
      · rw [u₃.rd, u₂.rd, u₁.rd]
      · rw [u₃.wr, u₂.wr, u₁.wr]
      · rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
      · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact (harg (by decide)).trans he.a3
      · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact (harg (by decide)).trans he.a4
      · rw [u₃.gpr, u₂.mem, u₁.mem]; exact (harg (by decide)).trans he.a2
    obtain ⟨⟨m', rd', wr', g', si, bp, dx⟩, x'⟩ := hh
    have ea : s'.ea (at_ .edx 0) = P.setWidth 64 := by
      show addr (s'.gpr .edx) 0 = _
      rw [dx, addr_zero]
    rw [WP.block_cons_iff]
    have hin' : InRegions (s'.rd ++ s'.wr) (P.setWidth 64) 16 := in_rd (hPin (wr'.trans wr₁))
    refine ⟨s'.setXmm .xmm0 (s'.mem.readW (P.setWidth 64) 128), by
      simp only [isa, reduceExec, State.load128, ea, hin', ite_true, Option.map_some], WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · refine hstable (rs := []) r₁ ⟨fun r h1 h2 h3 => by rw [gpr_setXmm]; exact g' r h1 h2 h3, fun r h0' _ => by
        rw [xmm_setXmm_of_ne _ _ h0', x'], by rw [rd_setXmm, rd'], by rw [wr_setXmm, wr']⟩
        (by rw [mem_setXmm, m']; exact Frame.refl _ _) fun _ hr => absurd hr List.not_mem_nil
    · rw [gpr_setXmm, si, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [gpr_setXmm, bp, Nat.sub_zero]
    · rw [gpr_setXmm, g' _ (by decide) (by decide) (by decide), esp₁]
    · rw [rd_setXmm, rd', rd₁]
    · rw [wr_setXmm, wr', wr₁]
    · rw [mem_setXmm, m']; exact fc
    · rw [xmm_setXmm_self, mem_setXmm, m', hP]
      exact hframe h0 f₁
  refine WP.seq (WP.mono (Q := Inv c w D N B Ready I s₀ N) ?_ fun s₃ h₃ => ?_)
  · refine WP.loop (M := isa) (body := c.body m) (c := .ne) (Q := Inv c w D N B Ready I s₀ N)
      (fun (n : Nat) (t : State) => ∃ j, n = N - j ∧ j < N ∧ Inv c w D N B Ready I s₀ j t) ?_ (N - 0) s₂
      ⟨0, rfl, hN, h₂⟩
    rintro n s ⟨k, rfl, hk, h⟩
    refine WP.mono (body_ok (Ready := Ready) (I := I) hc hm he ho hcore hstable hframe hstep hk h) fun s' ⟨h', z⟩ => ?_
    by_cases e : k + 1 = N
    · exact .inl ⟨by simp [eval, z, e], by rw [← e]; rw [← e] at h'; exact h'⟩
    · exact .inr ⟨by simp [eval, z, e], N - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, e], h'⟩
  · rw [show Chain.store = ([.mov .edx (.mem (argOp 2))] ++ [.movdquStore (at_ .edx 0) .xmm0] : List Instr) from rfl,
      WP.block_append_iff]
    refine WP.mono (Vperm.wp_g (Q := fun s' => Wp.Upd s₃ s' .edx P) rfl ?_) fun s' ⟨u, x'⟩ => ?_
    · refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 4 + 4 * 2) h₃.esp (hin h₃.rd h₃.wr (by decide)) fun s₄ u₄ =>
        WP.block_nil ?_
      have e := (arg_keep hc he ho h₃.frame (i := 2) (by decide)).trans he.a2
      exact ⟨u₄.gpr.trans e, u₄.other, u₄.mem, u₄.rd, u₄.wr, u₄.syms⟩
    have ea : s'.ea (at_ .edx 0) = P.setWidth 64 := by
      show addr (s'.gpr .edx) 0 = _
      rw [u.gpr, addr_zero]
    have hout := hPin (t := s') (u.wr.trans h₃.wr)
    rw [WP.block_cons_iff]
    refine ⟨{ s' with mem := s'.mem.writeW (P.setWidth 64) (s'.xmm .xmm0) }, by
      simp only [isa, reduceExec, State.store128, ea, hout, ite_true],
      WP.block_nil ⟨s₃.xmm .xmm0, s₃.mem, h₃.inv, h₃.frame, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show s'.mem.writeW _ _ = _
      rw [u.mem, x']
    · exact (u.other _ (by decide)).trans h₃.esi
    · exact (u.other _ (by decide)).trans h₃.esp
    · exact u.rd.trans h₃.rd
    · exact u.wr.trans h₃.wr

end

end VG.Proof.Aes.X86.Chain
