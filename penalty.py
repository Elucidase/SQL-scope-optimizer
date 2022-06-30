class Penalty:
    worth: int = 0
    def __init__(self, description):
        self.description = description
        
class NotIdempotentPenalty(Penalty):
    worth: int = 2
    
class UnsafeOnPredicatePenalty(Penalty):
    worth: int = 2

class RemovePredicatePenalty(Penalty):
    worth: int = 4
    
class CenterNotUniquePenalty(Penalty):
    worth: int = 2
    