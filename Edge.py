class Edge:

    def __init__(self, from_: int, to_: int):
        self.from_ = from_
        self.to_ = to_
        self.path_constraint = None
        self.color = 'black'

    def __str__(self) -> str:
        return '(%s, %s)' % (self.from_, self.to_)

    def __repr__(self) -> str:
        return '<%s object> (%s, %s)' % (self.__class__.__name__, self.from_, self.to_)

    def __eq__(self, other: 'Edge') -> bool:
        return self.from_ == other.from_ and self.to_ == other.to_

    def change_color(self):
        color = {'black': 'blue', 'blue': 'green', 'green': 'purple', 'purple': 'red', 'red': 'red'}
        self.color = color[self.color]

    def set_path_constraint(self, constraint):
        self.path_constraint = constraint
