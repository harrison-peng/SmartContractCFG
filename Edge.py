class Edge:

    def __init__(self, from_: int, to_: int):
        self.from_ = from_
        self.to_ = to_

    def __str__(self) -> str:
        return (self.from_, self.to_)

    def __repr__(self) -> str:
        return '<%s object> (%s, %s)' % (self.__class__.__name__, self.from_, self.to_)

    def __eq__(self, other):
        return self.from_ == other.from_ and self.to_ == other.to_