import LeanExperiments

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  IO.println "Theorems in LeanExperiments.Basic typechecked:"
  IO.println "  • even_add_even : NatEven m → NatEven n → NatEven (m + n)"
  IO.println "  • AddComm.add_comm : n + m = m + n"
