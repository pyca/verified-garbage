module
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutputCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.TailCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-! # FFDH on x86-64: successful scalar attempts use the shared exponentiation timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A checked scalar and its two full-width output buffers. -/
def WorkIn (p : GkP) (s : State) : Prop := ∃ rb mi,
  CheckPrivate.Work p.kp (p.xb rb) mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧
    p.mv = true ∧ Buffers p rb s

private def ReadyIn (p : GkP) (s : State) : Prop := ∃ rb,
  CheckPrivate.Ready p.kp (p.xb rb) s ∧ Buffers p rb s

private theorem work_inner (p : GkP) (s : State) (h : WorkIn p s) : CheckPrivate.Inner p.kp s := by
  obtain ⟨rb, mi, hw, hd, hm, _⟩ := h
  exact ⟨_, mi, hw, hd, hm⟩

private theorem work_ready (M : Mont) (R : R2Impl M) (p : GkP) (s : State) (h : WorkIn p s) :
    WP isa (.seq (.block r2Head) R.code) s (ReadyIn p) := by
  obtain ⟨rb, mi, hw, hd, hm, hb⟩ := h
  exact WP.mono (CheckPrivate.work_ready M R hw hd hm) fun _ ⟨hr, hi, _, k⟩ => ⟨rb, hr, hb.keep hi k⟩

private theorem ready_value (M : Mont) (E : CrtExpL M) (p : GkP) (s : State) (h : ReadyIn p s) :
    WP isa (seqs (pow M.mm E.code sG sK sX sXl)) s (ValueIn p) := by
  obtain ⟨rb, hr, hb⟩ := h
  exact WP.mono (CheckPrivate.ready_value M E hr) fun _ ⟨hv, hi, _, k⟩ => ⟨rb, hv, hb.keep hi k⟩

theorem tail_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two WorkIn)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail
  simp only [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two ReadyIn)
    (two_post (two_map GkP.kp work_inner
      ((CheckPrivate.r2_ct M R).mono (fun _ _ h => h) (fun _ _ _ => trivial))) (work_ready M R)) ?_)
  refine RelCT.seqs_append (a := pow M.mm E.code sG sK sX sXl)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput ++
      [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, .block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.status])
    (by simp [pow]) (by simp) (RelCT.seq (R := Two ValueIn)
      (two_post (two_map GkP.kp (fun _ _ h => by obtain ⟨_, hr, _⟩ := h; exact ⟨_, hr⟩)
        ((CheckPrivate.generator_power_ct M E hE).mono (fun _ _ h => h) (fun _ _ _ => trivial))) (ready_value M E)) ?_)
  exact RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.publicOutput]) (by simp)
    (RelCT.seq public_mask_ct mask_status_ct)

end VG.Proof.Ffdh.X86_64.GenerateKey
