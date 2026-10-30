module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fns
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point doubling and cached additions, in radix `2^64`, on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519R64.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64.Point64
open VG.Impl.X25519.X86_64 (baseline adx)
open VG.Spec.Ed25519.Point64 (doubleExtApi addCachedExtApi addCachedProjApi addAffineExtApi doubleContract
  addCachedContract addAffineContract)

def artifacts : List Artifact := [
  doubleExtApi.artifact X86_64.target {
    code := doubleFn baseline true
    verified := doubleExt_verified },
  addCachedExtApi.artifact X86_64.target {
    code := addFn baseline true
    verified := addExt_verified },
  addCachedProjApi.artifact X86_64.target {
    code := addFn baseline false
    verified := addProj_verified },
  doubleExtApi.artifact X86_64.target {
    suffix := "_adx"
    code := doubleFn adx true
    verified := doubleExtAdx_verified
    features := ["bmi2", "adx"] },
  addCachedExtApi.artifact X86_64.target {
    suffix := "_adx"
    code := addFn adx true
    verified := addExtAdx_verified
    features := ["bmi2", "adx"] },
  addCachedProjApi.artifact X86_64.target {
    suffix := "_adx"
    code := addFn adx false
    verified := addProjAdx_verified
    features := ["bmi2", "adx"] },
  addAffineExtApi.artifact X86_64.target {
    code := addAffineFn baseline
    verified := addAffine_verified },
  addAffineExtApi.artifact X86_64.target {
    suffix := "_adx"
    code := addAffineFn adx
    verified := addAffineAdx_verified
    features := ["bmi2", "adx"] }]

end VG.Artifacts.Ed25519R64.X86_64
