
# What is this?

This repo contains two things:

Elmo -- a prototype implementation of an embeddable Mongo-compatible database for
use in mobile apps

LSM -- a log structured merge tree storage engine (similar in concept to leveldb)

Elmo supports a pluggable store engine API, currently with two implementations,
one based on SQLite, and one based on the LSM library contained here.

LSM is not specific to Elmo or Mongo.  At some point it needs to move out into its
own repo as a general purpose library.

This stuff is *not* ready for production use.  It has no documentation.
Its file formats are still in flux.  Its code doesn't always follow Rust 
conventions very well (yet).

For more info, see the blog entry at 
[http://www.ericsink.com/entries/mobile\_sync\_for\_mongo.html](http://www.ericsink.com/entries/mobile_sync_for_mongo.html).

# Is this open source?

Yes.

# What's the license?

Apache License v2

# What language is this written in?

Rust (nightly).

The initial prototype was written in F#.  Some of that code is still hanging around
here for reference purposes.

# Why are you building this?

As part of our exploration of mobile sync solutions for Mongo.

For more info, see the blog entry mentioned near the top of this README.  

# Why is this called Elmo?

It stands for Embeddable Lite Mongo.

# Why is the LSM library called LSM?

Because it doesn't have a name yet.

