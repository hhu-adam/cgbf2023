import Lean

register_option pp.beta : Bool := {
  defValue := true,
  descr := "enable the 'unstructured proof' linter"
}