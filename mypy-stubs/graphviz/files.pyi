# Stubs for graphviz.files (Python 3.5)
#
# NOTE: This dynamically typed stub was automatically generated by stubgen.

from typing import Any, Optional

class Base:
    @property
    def format(self): ...
    @format.setter
    def format(self, format): ...
    @property
    def engine(self): ...
    @engine.setter
    def engine(self, engine): ...
    @property
    def encoding(self): ...
    @encoding.setter
    def encoding(self, encoding): ...
    def copy(self): ...

class File(Base):
    directory: str = ...
    filename: Any = ...
    format: Any = ...
    engine: Any = ...
    encoding: Any = ...
    def __init__(
        self,
        filename: Optional[Any] = ...,
        directory: Optional[Any] = ...,
        format: Optional[Any] = ...,
        engine: Optional[Any] = ...,
        encoding: Any = ...,
    ) -> None: ...
    def pipe(self, format: Optional[Any] = ...): ...
    @property
    def filepath(self): ...
    def save(self, filename: Optional[Any] = ..., directory: Optional[Any] = ...): ...
    def render(
        self,
        filename: Optional[Any] = ...,
        directory: Optional[Any] = ...,
        view: bool = ...,
        cleanup: bool = ...,
    ): ...
    def view(
        self,
        filename: Optional[Any] = ...,
        directory: Optional[Any] = ...,
        cleanup: bool = ...,
    ): ...

class Source(File):
    @classmethod
    def from_file(
        cls,
        filename,
        directory: Optional[Any] = ...,
        format: Optional[Any] = ...,
        engine: Optional[Any] = ...,
        encoding: Any = ...,
    ): ...
    source: Any = ...
    def __init__(
        self,
        source,
        filename: Optional[Any] = ...,
        directory: Optional[Any] = ...,
        format: Optional[Any] = ...,
        engine: Optional[Any] = ...,
        encoding: Any = ...,
    ) -> None: ...
