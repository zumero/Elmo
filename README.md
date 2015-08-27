
# What is this?

It's a prototype implementation of an embeddable Mongo-compatible database for
use in mobile apps.

This is *not* ready for production use.

For more info, see the blog entry at 
[http://www.ericsink.com/entries/mobile\_sync\_for\_mongo.html](http://www.ericsink.com/entries/mobile_sync_for_mongo.html).

# Is this open source?

Yes.

# What's the license?

Apache License v2

# What language is this written in?

Rust.

The initial prototype was written in F#.  The port to Rust is
in progress.

# Why are you building this?

As part of our exploration of mobile sync solutions for Mongo.

For more info, see the blog entry mentioned near the top of this README.  

# Why is this called Elmo?

It stands for Embeddable Lite Mongo.

# lsm

A key-value store built on a Log Structured Merge Tree.

# server

The server and wire protocol parts of Elmo.
This code exists primarily for the purpose of
allowing the MongoDB test suite to be run against the
Elmo database library.

## storage/sqlite3

An implementation of Elmo's storage API which uses SQLite as
a storage layer.

## misc

A library of common utility stuff that is used by the 
projects above.

