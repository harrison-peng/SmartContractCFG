class Edge:

    def __init__(self, from_: int, to_: int, color: str = 'black'):
        self.from_ = from_
        self.to_ = to_
        self.path_constraint = None
        self.color = color

    def __str__(self) -> str:
        return '(%s, %s)' % (self.from_, self.to_)

    def __repr__(self) -> str:
        return '<%s object> (%s, %s)' % (self.__class__.__name__, self.from_, self.to_)

    def __eq__(self, other: 'Edge') -> bool:
        return self.from_ == other.from_ and self.to_ == other.to_

    def change_color(self):
        color = {'black': 'red', 'red': 'orange', 'orange': 'green', 'green': 'blue', 'blue': 'purple', 'purple': 'purple'}
        self.color = color[self.color]

    def set_path_constraint(self, constraint):
        self.path_constraint = constraint
