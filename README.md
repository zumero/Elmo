
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

# Why is this written in F#?

Because it's an exploratory prototype, and that was the fastest way to
develop it.

# Will this stay in F# as the only implementation?

A port to Rust is in progress.  That port is happening over in
this repo:

https://github.com/ericsink/LSM

Which is a temporary living arrangement.

# Why are you building this?

As part of our exploration of mobile sync solutions for Mongo.

For more info, see the blog entry mentioned near the top of this README.  

# Why is this called Elmo?

It stands for Embeddable Lite Mongo.

# How complete is this?

Most CRUD operations work just like they do in Mongo.

Intentionally omitted:  Sharding, JavaScript

Not done yet:  Full text search, geo, indexes

Number of passing test cases in jstests:  Over 300

For more info, see the blog entry mentioned near the top of this README.  

# How can you be running Mongo's jstests on an "embedded" database?  

Elmo has a server which was written specifically for that purpose.



# Overview

NOTE:  Nothing here is ready for production use.

This repo contains a bunch of database stuff in Rust:

## lsm

A key-value store built on a Log Structured Merge Tree.

This library was originally written in C#, and that version of the code
exists in the history of this repo somewhere.  

Then it was
ported to F#, and that version is in the fsharp directory.

Then it was ported to Rust.

## elmo

A NoSQL/document database aimed primarily at mobile use.
This is a Rust port of https://github.com/zumero/Elmo

## bson

The BSON code from Elmo, separated out as a library.

## server

The server and wire protocol parts of Elmo, separated out as
a library.  This code exists primarily for the purpose of
allowing the MongoDB test suite to be run against the
Elmo database library.

## storage/sqlite3

An implementation of Elmo's storage API which uses SQLite as
a storage layer.

## misc

A library of common utility stuff that is used by the 
projects above.

# Status

For LSM, the port from F# to Rust is mostly complete.

For all the ELmo stuff, the Rust port is just getting started.

# License

Apache v2


