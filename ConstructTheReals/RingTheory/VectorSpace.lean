import ConstructTheReals.RingTheory.Module
import ConstructTheReals.RingTheory.Field

class VectorSpace (F: Type u) (X: Type v) [Field F] [CommGroup X] extends Module X F
