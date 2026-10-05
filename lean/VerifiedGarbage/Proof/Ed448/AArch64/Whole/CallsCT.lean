import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CT
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge

/-!
# Ed448's complete operations on AArch64: each call in constant time

The sponge's pieces (`zeroSt_ct`, `kabs_ct`, `kpad_ct`, `ksqz_ct`) and the
calls of the Ed448 primitives (`reduce_ct`, `base_ct`, `mulAdd_ct`,
`equation_ct`), related by `Two`: their arguments have values that agree in
both runs (`val`, or the sponge's positions), which are the callee's public
data, and each run has the effect its correctness lemma gives (`hok`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {V : Env} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
  {M : Mem → Prop} {d : Nat} {scr : Addr}

theorem regs_get {args : List (Reg × Src)} {val : Reg → Addr} {t : State} (h : Regs args val t) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : t.gpr r = val r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

theorem entry_eq {args : List (Reg × Src)} {a b : State}
    (h : ∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) {r : Reg}
    (hr : r ∈ args.map Prod.fst) : a.callEntry.gpr r = b.callEntry.gpr r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

/-! ## The sponge -/

theorem zeroSt_ct (hV : V.Ok) (hs : ScrOk V d scr) (h₁ : M m₁) (h₂ : M m₂) {P : State → Prop}
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS [(.x15, .loc d 0)])) hint).isSome = true) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (zeroSt d) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
    (fun _ h => WP.mono (zeroSt_ok hV hs h.1) fun _ hu => ⟨hu.1, trivial⟩)
  refine (setupS_ct hV h₁ h₂ (args := [(.x15, .loc d 0)]) (by simp) (by simp [srcValid, hd.1]; omega) rfl
    (by simp [preserved]) ht (fun _ => scr) fun _ hc _ p hp => ?_).seq ?_
  · rw [List.mem_singleton.mp hp, hs.loc hc, BitVec.add_zero]
  · refine RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨two_sp h, fun r hr => ?_⟩)
      (by taint_decide)
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    exact (h.1.2 _ List.mem_cons_self).trans (h.2.2 _ List.mem_cons_self).symm

/-- What `absArgs` puts in the registers. -/
def absVal (scr dp : Addr) (n q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => dp
  | .x4 => BitVec.ofNat 64 n
  | _ => scr + BitVec.ofNat 64 256

theorem kabs_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {src len pos : Src} (hvs : srcValid src) (hvl : srcValid len)
    (hvp : srcValid pos) (hrs : noRet src = true) (hrl : noRet len = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (absArgs d src len pos))) hint).isSome = true)
    {P : State → Prop} {dp : Addr} {n q : Nat}
    (hdp : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kabs v.callee d src len pos)
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 ((q + n) % 136)) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · exact hvs
      · exact hvl
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hrs, hrl]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (absVal scr dp n q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (fun hc hr => absorb_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x3, src) (by simp)) (hr (.x4, len) (by simp)) (hr (.x5, .loc d 256) (by simp))
      hql hnl dS dK kD)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hin) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x3, src) (by simp), hg (.x4, len) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kabs_ok v hV hs hc hvs hvl hvp hrs hrl (hdp hm hc hp) (hn hm hc hp)
      (hq hm hc hp) hql hnl hin dS dK kD) fun _ ⟨hu, _, _, hx⟩ =>
        ⟨hu, BitVec.eq_of_toNat_eq (by rw [hx, toNat_ofNat64 (by omega)])⟩)
  simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · exact hdp hm hc hp
  · exact hn hm hc hp
  · exact hs.loc hc _ 256

/-- What `padArgs` puts in the registers. -/
def padVal (scr : Addr) (q : Nat) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 q
  | .x3 => BitVec.ofNat 64 0x1f
  | _ => scr + BitVec.ofNat 64 256

theorem kpad_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {pos : Src} (hvp : srcValid pos)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (padArgs d pos))) hint).isSome = true)
    {P : State → Prop} {q : Nat}
    (hq : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q)
    (hql : q < 136) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (kpad v.callee d pos) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0x1f : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (padVal scr q) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun hc hr => pad_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, pos) (by simp)) (hr (.x4, .loc d 256) (by simp)) hql)
    (covers_rw (by simp) hs.sponge_writes) hs.sponge_writes
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, pos) (by simp),
      hg (.x4, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (kpad_ok v hV hs hc hvp (hq hm hc hp) hql) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exact hq hm hc hp
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hs.loc hc _ 256

/-- What `sqzArgs` puts in the registers. -/
def sqzVal (scr op : Addr) : Reg → Addr
  | .x0 => scr
  | .x1 => BitVec.ofNat 64 136
  | .x2 => BitVec.ofNat 64 0
  | .x3 => op
  | .x4 => BitVec.ofNat 64 114
  | _ => scr + BitVec.ofNat 64 256

theorem ksqz_ct (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (h₁ : M m₁) (h₂ : M m₂) {out : Src} (hvo : srcValid out) (hro : noRet out = true)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS (sqzArgs d out))) hint).isSome = true)
    {P : State → Prop} {op : Addr}
    (hop : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → srcValue V.E t.mem (t.gpr .x0) out = op)
    (hw : Apart V ⟨op, 114⟩ ∨ ∃ R ∈ V.outs, Within ⟨op, 114⟩ R)
    (dS : Region.Disjoint ⟨op, 114⟩ (ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P) (ksqz v.callee d out) (Two V g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  have hws : ∀ r ∈ [ST scr, ⟨op, 114⟩, KS scr], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr ⟨_, hs.out, st_within scr⟩
    · exact hw
    · exact .inr ⟨_, hs.out, ks_within scr⟩
  refine callS_ct hV h₁ h₂ (by simp) (fun p hp => by
      simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0 : Nat) < 65536; decide
      · exact hvo
      · show (114 : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hro]; rfl) (by simp [preserved])
    (by simp [linkRegs]) ht (sqzVal scr op) (fun hm hc hp p hp' => ?_)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (fun hc hr => squeeze_pre hV hs hc.1.sp (hr (.x0, .loc d 0) (by simp)) (hr (.x1, .val (.const 136)) (by simp))
      (hr (.x2, .val (.const 0)) (by simp)) (hr (.x3, out) (by simp)) (hr (.x4, .val (.const 114)) (by simp)) (hr (.x5, .loc d 256) (by simp))
      dS dK kD)
    (covers_rw (by simp) hws) hws
    (fun _ _ hsp hg => ⟨hg (.x0, .loc d 0) (by simp), hg (.x1, .val (.const 136)) (by simp), hg (.x2, .val (.const 0)) (by simp),
      hg (.x3, out) (by simp), hg (.x4, .val (.const 114)) (by simp), hg (.x5, .loc d 256) (by simp), hsp⟩)
    (fun hm hc hp => WP.mono (ksqz_ok v hV hs hc hvo hro (hop hm hc hp) hw dS dK kD)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩)
  simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hs.loc hc _ 0).trans (BitVec.add_zero _)
  · rfl
  · rfl
  · exact hop hm hc hp
  · rfl
  · exact hs.loc hc _ 256

/-! ## The Ed448 primitives -/

theorem reduce_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hd : Region.Disjoint ⟨val .x1, 114⟩ ⟨val .x2, 8192⟩) (hrd : Readable V ⟨val .x1, 114⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarReduce_ok
    Proof.Ed448.AArch64.scalarReduce_ct
    (fun _ hs => reduce_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hd)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hrd) hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp))⟩) hok

theorem base_ct (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂)
    {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2], r ∈ args.map Prod.fst)
    (hos : Region.Disjoint ⟨val .x0, 57⟩ ⟨val .x2, 8192⟩) (hss : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x2, 8192⟩)
    (hnc : (val .x2).toNat + 8192 ≤ 2 ^ 64) (hrd : Readable V ⟨val .x1, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x2, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x2, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval hb.ok
    hb.ct
    (fun _ hs => base_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) hos hss hnc)
    (covers_rw (fun r hr => by rw [List.mem_singleton.mp hr]; exact hrd) hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp))⟩) hok

theorem mulAdd_ct (hV : V.Ok) (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4], r ∈ args.map Prod.fst)
    (hdr : Region.Disjoint ⟨val .x1, 57⟩ ⟨val .x4, 8192⟩) (hdk : Region.Disjoint ⟨val .x2, 57⟩ ⟨val .x4, 8192⟩)
    (hds : Region.Disjoint ⟨val .x3, 57⟩ ⟨val .x4, 8192⟩)
    (hrr : Readable V ⟨val .x1, 57⟩) (hrk : Readable V ⟨val .x2, 57⟩) (hrs : Readable V ⟨val .x3, 57⟩)
    (hwo : Writable V ⟨val .x0, 57⟩) (hws : Writable V ⟨val .x4, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x4, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  have hrd : ∀ r ∈ [(⟨val .x1, 57⟩ : Region), ⟨val .x2, 57⟩, ⟨val .x3, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrr, hrk, hrs]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval Proof.Ed448.AArch64.scalarMulAdd_ok
    Proof.Ed448.AArch64.scalarMulAdd_ct
    (fun _ hs => mulAdd_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) (regs_get hs (hm .x4 (by simp)))
      hdr hdk hds)
    (covers_rw hrd hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), entry_eq hg (hm .x3 (by simp)), entry_eq hg (hm .x4 (by simp))⟩) hok

theorem equation_ct (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (hV : V.Ok)
    (h₁ : M m₁) (h₂ : M m₂) {args : List (Reg × Src)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, srcValid p.2) (hret : retOk args = true)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setupS args)) hint).isSome = true)
    {P : State → Prop} (val : Reg → Addr)
    (hval : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t →
      ∀ p ∈ args, srcValue V.E t.mem (t.gpr .x0) p.2 = val p.1)
    (hm : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], r ∈ args.map Prod.fst)
    (hdp : Region.Disjoint ⟨val .x0, 57⟩ ⟨val .x3, 8192⟩) (hds : Region.Disjoint ⟨val .x1, 114⟩ ⟨val .x3, 8192⟩)
    (hdc : Region.Disjoint ⟨val .x2, 57⟩ ⟨val .x3, 8192⟩) (hnc : (val .x3).toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨val .x0, 57⟩) (hrs : Readable V ⟨val .x1, 114⟩) (hrc : Readable V ⟨val .x2, 57⟩)
    (hws : Writable V ⟨val .x3, 8192⟩) {Q : State → Prop}
    (hok : ∀ {g vec m₀ t}, M m₀ → WCtx V g vec m₀ t → P t → WP isa
      (callS args "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) t
      fun u => WCtx V g vec m₀ u ∧ Q u) :
    RelCT isa (Two V g₁ g₂ v₁ v₂ m₁ m₂ P)
      (callS args "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation)
      (Two V g₁ g₂ v₁ v₂ m₁ m₂ Q) := by
  have hw : ∀ r ∈ [(⟨val .x3, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact hws
  have hrd : ∀ r ∈ [(⟨val .x0, 57⟩ : Region), ⟨val .x1, 114⟩, ⟨val .x2, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrp, hrs, hrc]
  exact callS_ct hV h₁ h₂ hn hv hret hr hl ht val hval (Proof.Ed448.AArch64.verifyEquation_ok hR hE)
    Proof.Ed448.AArch64.verifyEquation_ct
    (fun _ hs => equation_pre (regs_get hs (hm .x0 (by simp))) (regs_get hs (hm .x1 (by simp)))
      (regs_get hs (hm .x2 (by simp))) (regs_get hs (hm .x3 (by simp))) hdp hds hdc hnc)
    (covers_rw hrd hw) hw
    (fun _ _ hsp hg => ⟨hsp, entry_eq hg (hm .x0 (by simp)), entry_eq hg (hm .x1 (by simp)),
      entry_eq hg (hm .x2 (by simp)), entry_eq hg (hm .x3 (by simp))⟩) hok

end VG.Proof.Ed448.AArch64.Whole
